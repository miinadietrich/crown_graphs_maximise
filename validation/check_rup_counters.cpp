/* Independent RUP checker using occurrence counts and XOR, not watched literals.
 * Every clause keeps the count and XOR of its non-false literals. Assigning a
 * variable visits every occurrence of its falsified literal. Temporary updates
 * are explicitly reversed after each RUP test. No SAT library is used.
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
struct Clause {std::vector<int> literals; int remaining; unsigned parity;};
class Checker {
    int n; std::vector<int> value, trail;
    std::vector<Clause> clauses;
    std::vector<std::vector<int>> occurrences;
    std::size_t head=0;
    static unsigned code(int l){return 2u*unsigned(std::abs(l))+unsigned(l<0);}
    static int literal(unsigned c){return (c&1)?-int(c/2):int(c/2);}
    int eval(int l) const{return (l>0?1:-1)*value[std::abs(l)];}
    bool enqueue(int l){int v=std::abs(l),sgn=l>0?1:-1;
        if(value[v])return value[v]==sgn;value[v]=sgn;trail.push_back(l);return true;}
    bool normalize(std::vector<int>& c){
        for(int l:c)if(std::abs(l)<1||std::abs(l)>n)throw std::runtime_error("bad variable");
        std::sort(c.begin(),c.end());c.erase(std::unique(c.begin(),c.end()),c.end());
        for(int l:c)if(std::binary_search(c.begin(),c.end(),-l))return false;
        return true;
    }
    bool propagate(){
        while(head<trail.size()){
            unsigned neg=code(-trail[head++]);bool conflict=false;
            for(int id:occurrences[neg]){
                auto& c=clauses[id];--c.remaining;c.parity^=neg;
                if(c.remaining==0)conflict=true;
                else if(c.remaining==1&&!conflict&&!enqueue(literal(c.parity)))conflict=true;
            }
            if(conflict)return false;
        }
        return true;
    }
public:
    bool inconsistent=false;
    explicit Checker(int vars):n(vars),value(n+1,0),occurrences(2*n+4){}
    void add(std::vector<int> c){
        if(inconsistent||!normalize(c))return;
        int id=int(clauses.size()),remaining=0;unsigned parity=0;
        for(int l:c){occurrences[code(l)].push_back(id);if(eval(l)>=0){++remaining;parity^=code(l);}}
        clauses.push_back({std::move(c),remaining,parity});
        if(!remaining){inconsistent=true;return;}
        if(remaining==1&&!enqueue(literal(parity))){inconsistent=true;return;}
        if(!propagate())inconsistent=true;
    }
    bool rup(std::vector<int> c){
        if(inconsistent||!normalize(c))return true;
        std::size_t root=trail.size();bool conflict=false;
        for(int l:c)if(!enqueue(-l)){conflict=true;break;}
        if(!conflict)conflict=!propagate();
        // Only assignments before head have changed counters. Restore those
        // occurrences before clearing both processed and queued assignments.
        for(std::size_t i=root;i<head;++i){unsigned neg=code(-trail[i]);
            for(int id:occurrences[neg]){++clauses[id].remaining;clauses[id].parity^=neg;}}
        while(trail.size()>root){value[std::abs(trail.back())]=0;trail.pop_back();}
        head=root;return conflict;
    }
};
int main(int argc,char**argv){try{
    if(argc!=3)throw std::runtime_error("usage: check_rup_counters input.cnf proof.rup");
    auto started=std::chrono::steady_clock::now();
    std::ifstream in(argv[1]);if(!in)throw std::runtime_error("cannot open CNF");
    std::string line;int n=0;std::uint64_t expected=0,original=0,checked=0;
    while(std::getline(in,line)){if(line.empty()||line[0]=='c')continue;
        std::istringstream s(line);std::string p,fmt;s>>p>>fmt>>n>>expected;
        if(p!="p"||fmt!="cnf"||n<=0)throw std::runtime_error("bad header");break;}
    Checker checker(n);std::vector<int> c;
    while(std::getline(in,line)){if(line.empty()||line[0]=='c')continue;
        std::istringstream s(line);int l;while(s>>l){if(l)c.push_back(l);else{checker.add(c);c.clear();++original;}}}
    if(original!=expected||!c.empty())throw std::runtime_error("bad clause count");
    std::ifstream proof(argv[2]);if(!proof)throw std::runtime_error("cannot open proof");
    while(!checker.inconsistent&&std::getline(proof,line)){
        if(line.empty()||line[0]=='c')continue;
        std::istringstream s(line);int l;bool ended=false;c.clear();
        while(s>>l){if(!l){ended=true;break;}c.push_back(l);}
        if(!ended)throw std::runtime_error("malformed addition");
        if(!checker.rup(c))throw std::runtime_error("non-RUP addition "+std::to_string(checked+1));
        ++checked;checker.add(c);
    }
    if(!checker.inconsistent)throw std::runtime_error("no contradiction");
    std::cout<<"{\"verified_unsat\":true,\"original_clauses\":"<<original
        <<",\"additions_checked\":"<<checked<<",\"method\":\"occurrence_counts\",\"seconds\":"
        <<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<"}\n";
}catch(const std::exception& e){std::cerr<<"VERIFICATION FAILED: "<<e.what()<<"\n";return 1;}}
