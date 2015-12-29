
s" stdlib.fs" included
s" golf_lang.fs" included
s" golf_preprocess.fs" included

: get-filename
next-arg dup 0= if
    s" usage: <golfscriptfile>" type cr
    bye
then
;

: dump_stack
depth 0 +do 
    val_dump cr
LOOP
;


: golf-stdin 

    begin 
    
        s" golf$" type cr
        1024 allocate throw { buf } 
        buf 1024 stdin read-line throw 
    
        while 
        buf swap 
        
            golf-preprocess
            get-order golf-wordlist swap 1+ set-order
            execute
            get-order nip 1- set-order
            dump_stack
   repeat 
; 


golf-stdin 
bye

