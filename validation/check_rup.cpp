/* Stand-alone reverse-unit-propagation proof checker.
 * It does not link Z3 or trust the solver. The original CNF is authoritative.
 * Every proof addition, INCLUDING Z3's 'i' records, is checked by assuming
 * its negation and performing Boolean unit propagation. Deletions are ignored:
 * retaining previously justified clauses is sound for RUP checking.
 * No RAT or extension steps are accepted. A checked contradiction is required.
 */
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

class Checker {
    int n;
    std::vector<int8_t> value;
    std::vector<std::vector<int>> clauses, watches;
    std::vector<int> trail, marks;
    std::size_t head=0;
    int stamp=0;
public:
    bool inconsistent=false;
    explicit Checker(int variables):n(variables),value(n+1,0),watches(2*n+4),marks(n+1,0){}
    static unsigned index(int literal){return 2u*unsigned(std::abs(literal))+unsigned(literal<0);}
    int eval(int literal) const {return literal>0?value[literal]:-value[-literal];}
    bool enqueue(int literal){
        int v=std::abs(literal), target=literal>0?1:-1;
        if(value[v])return value[v]==target;
        value[v]=int8_t(target);trail.push_back(literal);return true;
    }
    bool normalize(std::vector<int>& c){
        ++stamp;std::size_t out=0;
        for(int x:c){
            int v=std::abs(x);
            if(v<1||v>n)throw std::runtime_error("undeclared proof variable");
            int tag=x>0?stamp:-stamp;
            if(marks[v]==-tag)return false; // tautology
            if(marks[v]!=tag){marks[v]=tag;c[out++]=x;}
        }
        c.resize(out);return true;
    }
    bool propagate(){
        while(head<trail.size()){
            int false_literal=-trail[head++];auto& w=watches[index(false_literal)];
            std::size_t j=0;
            while(j<w.size()){
                int id=w[j];auto& c=clauses[id];
                if(c[0]!=false_literal)std::swap(c[0],c[1]);
                if(c[0]!=false_literal)throw std::runtime_error("broken watch invariant");
                if(eval(c[1])>0){++j;continue;}
                std::size_t replacement=2;
                while(replacement<c.size()&&eval(c[replacement])<0)++replacement;
                if(replacement<c.size()){
                    std::swap(c[0],c[replacement]);
                    watches[index(c[0])].push_back(id);
                    w[j]=w.back();w.pop_back();
                }else{
                    if(eval(c[1])<0||!enqueue(c[1]))return false;
                    ++j;
                }
            }
        }
        return true;
    }
    void add(std::vector<int> c){
        if(inconsistent||!normalize(c))return;
        std::vector<int> available;
        for(std::size_t j=0;j<c.size();++j){
            int v=eval(c[j]);if(v>0)return; // true at the permanent root level
            if(v==0)available.push_back(int(j));
        }
        if(available.empty()){inconsistent=true;return;}
        if(available.size()==1){
            if(!enqueue(c[available[0]]))inconsistent=true;
            // A root-unit clause need not be watched: its assignment is permanent.
            return;
        }
        std::swap(c[0],c[available[0]]);
        // available[1] cannot be zero and was not moved by the first swap.
        std::swap(c[1],c[available[1]]);
        int id=int(clauses.size());clauses.push_back(std::move(c));
        watches[index(clauses[id][0])].push_back(id);
        watches[index(clauses[id][1])].push_back(id);
    }
    void root_propagate(){if(!inconsistent&&!propagate())inconsistent=true;}
    bool rup(std::vector<int> c){
        if(inconsistent)return true;
        if(!normalize(c))return true;
        std::size_t root=trail.size();bool conflict=false;
        for(int x:c)if(!enqueue(-x)){conflict=true;break;}
        if(!conflict)conflict=!propagate();
        while(trail.size()>root){value[std::abs(trail.back())]=0;trail.pop_back();}
        head=root;return conflict;
    }
};

int main(int argc,char**argv){
    try{
        if(argc!=3)throw std::runtime_error("usage: check_rup input.cnf proof.drat");
        auto start=std::chrono::steady_clock::now();
        std::ifstream in(argv[1]);if(!in)throw std::runtime_error("cannot open CNF");
        std::string line;int variables=0;std::uint64_t promised=0;
        while(std::getline(in,line)){
            if(line.empty()||line[0]=='c')continue;
            std::istringstream s(line);std::string p,fmt;s>>p>>fmt>>variables>>promised;
            if(p!="p"||fmt!="cnf"||variables<=0)throw std::runtime_error("bad CNF header");
            break;
        }
        Checker checker(variables);std::uint64_t original=0;
        std::vector<int> c;
        while(std::getline(in,line)){
            if(line.empty()||line[0]=='c')continue;
            std::istringstream s(line);int x;
            while(s>>x){if(x)c.push_back(x);else{checker.add(c);c.clear();++original;}}
        }
        if(!c.empty()||original!=promised)throw std::runtime_error("CNF clause count mismatch");
        checker.root_propagate();
        std::ifstream proof(argv[2]);if(!proof)throw std::runtime_error("cannot open proof");
        std::uint64_t step=0, inputs=0, additions=0, deletions=0;
        while(!checker.inconsistent&&std::getline(proof,line)){
            ++step;if(line.empty()||line[0]=='c')continue;
            char kind=(line[0]=='i'||line[0]=='d')?line[0]:'a';
            if(kind=='d'){++deletions;continue;}
            std::istringstream s(kind=='i'?line.substr(1):line);c.clear();int x;bool ended=false;
            while(s>>x){if(x==0){ended=true;break;}c.push_back(x);}
            if(!ended)throw std::runtime_error("unterminated proof clause");
            if(!checker.rup(c))throw std::runtime_error("non-RUP clause at proof line "+std::to_string(step));
            checker.add(c);checker.root_propagate();
            if(kind=='i')++inputs;else ++additions;
        }
        if(!checker.inconsistent)throw std::runtime_error("proof did not derive a contradiction");
        double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        std::cout<<"{\"verified_unsat\":true,\"original_clauses\":"<<original
          <<",\"input_records_checked\":"<<inputs<<",\"additions_checked\":"<<additions
          <<",\"deletions_ignored\":"<<deletions<<",\"proof_lines_read\":"<<step
          <<",\"seconds\":"<<seconds<<"}\n";
    }catch(const std::exception& e){std::cerr<<"VERIFICATION FAILED: "<<e.what()<<"\n";return 1;}
}
