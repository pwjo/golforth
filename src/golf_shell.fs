
s" stdlib.fs" included
s" golf_lang.fs" included
s" golf_parser.fs" included


: dump_stack ( * -- ) 
depth 0 +do 
    val_dump cr
LOOP
;


: golf-prompt ( -- )

    s" golf$" type cr
;


: golf-execute ( xt -- )

    get-order golf-wordlist swap 1+ set-order
    execute
    get-order nip 1- set-order
;


: golf-stdin ( -- )

    1024 allocate throw { buf } 

    begin 
    
        golf-prompt
        buf 1024 stdin read-line throw 
    

        while 
            buf swap 

            golf-parse
            golf-execute

            dump_stack
   repeat 
; 


golf-stdin 
bye

