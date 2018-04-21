function check(){
 ./test.sh examples/$1.c;
 printf '\n~~~~~\n';
 python Parser.py examples/$1.c;
 printf '\n~~~~~\n';
 diff -b -B -E -Z -w examples/$1.c2.s examples/$1.c.s;
 printf '\n~~~~~\n';
 diff -b -B -E -Z -w examples/$1.c2.cfg examples/$1.c.cfg;
 printf '\n~~~~~\n';
 # diff -b -B -E -Z -w examples/$1.c2.sym examples/$1.c.sym;
 # printf '\n~~~~~\n';
 diff -b -B -E -Z -w examples/$1.c2.ast examples/$1.c.ast;
}