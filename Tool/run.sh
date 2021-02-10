TIMEFORMAT=%R #user time

file1="result_v1.txt"

#export DYLD_LIBRARY_PATH=/Users/jasminexuereb/.opam/4.08.0/lib/z3
#echo $DYLD_LIBRARY_PATH 

run(){
   [ -f $file1 ] && rm $file1
   for i in `seq 10`; #repeat for 10 times
     do 
       # { time ./main.native "$*" ;} > /dev/null 2>> $file1 #hide program output and redirect time to results_v1.txt
       time ./main.native "$*" 2>> $file1 #hide program output and redirect time to results_v1.txt
       #/usr/bin/time -f "%e" -o $file1 --append ./trial_v1/main.native "$*"; #redirect output to result_v1.txt
   	  done
}

run "k<x>.1"

#run "let x = 5 in (a<x>.if x<2 then k<5>.2 else k<5>.1) + (a<x>.if ((x<2)&(x>0)) then k<5>.2 else k<5>.1)"

