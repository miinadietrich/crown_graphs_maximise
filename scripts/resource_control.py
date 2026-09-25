"""Build argument-preserving ELF wrappers with a compiler concurrency limit."""
from pathlib import Path
import argparse
import json
import subprocess
from common import digest, save

COMMON = r'''
#define _POSIX_C_SOURCE 200809L
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <time.h>
static void fail(const char *s) { perror(s); exit(125); }
'''
LAKE = r'''
int main(int argc, char **argv) {
 (void)argc;
 char *cwd=getcwd(NULL,0); if(!cwd)fail("getcwd");
 if(mkdir(".lake",0777)!=0 && errno!=EEXIST)fail("mkdir .lake");
 size_t n=0; while(cwd[n])n++;
 char *lock=malloc(n+40); if(!lock)fail("malloc");
 snprintf(lock,n+40,"%s/.lake/crown-lean.lock",cwd);
 if(setenv("CROWN_COMPILER_LOCK",lock,1)||setenv("LEAN_NUM_THREADS",COMPILER_WORKERS,1)||
    setenv("LAKE_OVERRIDE_LEAN","true",1)||setenv("LEAN_SYSROOT",WRAPPED_SYSROOT,1))fail("setenv");
 argv[0]=REAL_LAKE; execv(REAL_LAKE,argv); perror("exec Lake"); return 127;
}
'''
LEAN = r'''
int main(int argc, char **argv) {
 (void)argc;
 if(setenv("LEAN_NUM_THREADS","1",1))fail("set compiler threads");
 const char *lock=getenv("CROWN_COMPILER_LOCK");
 if(!lock || !*lock) { fputs("Missing compiler lock\n",stderr); return 125; }
 int fd=-1;
 if(COMPILER_JOBS==1) {
  fd=open(lock,O_CREAT|O_RDWR,0600); if(fd<0)fail("open lock");
  while(flock(fd,LOCK_EX)!=0) { if(errno!=EINTR)fail("lock compiler"); }
 } else {
  size_t size=strlen(lock)+32;
  char *slot=malloc(size); if(!slot)fail("malloc lock slot");
  while(fd<0) {
   for(unsigned i=0;i<COMPILER_JOBS;i++) {
    unsigned index=((unsigned)getpid()+i)%COMPILER_JOBS;
    snprintf(slot,size,"%s.%u",lock,index);
    int candidate=open(slot,O_CREAT|O_RDWR,0600); if(candidate<0)fail("open lock slot");
    if(flock(candidate,LOCK_EX|LOCK_NB)==0) { fd=candidate; break; }
    int error=errno; close(candidate);
    if(error!=EWOULDBLOCK && error!=EAGAIN && error!=EINTR) { errno=error; fail("lock compiler slot"); }
   }
   if(fd<0) { struct timespec delay={0,50000000}; nanosleep(&delay,NULL); }
  }
  free(slot);
 }
 if(fd<3) { int high=fcntl(fd,F_DUPFD,3); if(high<0)fail("duplicate lock fd"); close(fd); fd=high; }
 /* Retain the descriptor across exec and preserve every argument. */
 argv[0]=REAL_LEAN; execv(REAL_LEAN,argv); perror("exec Lean"); return 127;
}
'''


def install(toolchain, destination, jobs=1):
    if not isinstance(jobs, int) or not 1 <= jobs <= 64:
        raise ValueError("Compiler concurrency must be between 1 and 64")
    real = Path(toolchain).resolve(strict=True)
    base = Path(destination).resolve()
    if base.exists():
        raise RuntimeError(f"Refusing an existing wrapper directory: {base}")
    (base / "bin").mkdir(parents=True)
    (base / "sysroot/bin").mkdir(parents=True)
    for child in real.iterdir():
        if child.name != "bin" and child != base and not child.name.startswith("crown-"):
            (base / "sysroot" / child.name).symlink_to(child, target_is_directory=child.is_dir())
    for child in (real / "bin").iterdir():
        if child.name != "lean":
            (base / "sysroot/bin" / child.name).symlink_to(child)
    prefix = "".join(f"#define {name} {json.dumps(str(value))}\n" for name, value in [
        ("REAL_LEAN", real / "bin/lean"), ("REAL_LAKE", real / "bin/lake"),
        ("WRAPPED_SYSROOT", base / "sysroot")])
    prefix += f"#define COMPILER_JOBS {jobs}\n"
    prefix += f'#define COMPILER_WORKERS "{jobs}"\n'
    commands = []
    for name, body, target in [("lake", LAKE, "bin/lake"), ("lean", LEAN, "sysroot/bin/lean")]:
        source = base / (name + ".c")
        source.write_text(prefix + COMMON + body, encoding="utf-8")
        command = ["cc", "-O2", "-Wall", "-Wextra", "-Werror", "-o", str(base / target), str(source)]
        subprocess.run(command, check=True)
        commands.append(command)
    report = {"compiler_jobs": jobs, "toolchain": str(real), "path_entry": str(base / "bin"), "sysroot": str(base / "sysroot"),
              "commands": commands, "files": [{"path": str(p), "sha256": digest(p)} for p in
              [real / "bin/lean", real / "bin/lake", base / "bin/lake", base / "sysroot/bin/lean", base / "lake.c", base / "lean.c"]]}
    save(base / "installation.json", report)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("toolchain", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--compiler-jobs", type=int, default=1)
    args = parser.parse_args()
    print(json.dumps(install(args.toolchain, args.destination, args.compiler_jobs), indent=2))
