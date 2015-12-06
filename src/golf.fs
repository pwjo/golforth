
s" golf_preprocess.fs" included
s" golf_lang.fs" included

: get-filename
next-arg dup 0= if
    s" usage: <golfscriptfile>" type cr
    bye
then
;

: dump_stack
depth 0 +do 
    val .
LOOP
;

get-filename slurp-file  

golf-preprocess

evaluate

dump_stack cr

