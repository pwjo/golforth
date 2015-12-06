s" regex/regex.fth" included

S\" ^[a-zA-Z_][a-zA-Z0-9_]*" regex$ constant rgx-variable-string
S\" ^'((?:\\\\.|[^'])*)'?" regex$ constant rgx-string-single
S\" ^\"((?:\\\\.|[^\"])*)\"?" regex$ constant rgx-string-double
S\" ^-?[0-9]+" regex$ constant rgx-integer
S\" ^#[^\\n\\r]*" regex$ constant rgx-comment
S\" ^:" regex$ constant rgx-store
S\" ^." regex$ constant rgx-variable-char


create mapping-operators
s" ~" , , s" golf_sim" , ,
s" +" , , s" golf_+" , ,
0 ,


create append-buffer 4096 chars allot

: get-mapping { caddr u map-table --  caddr u | caddr1 u1 }

    0 map-table ?DO
        
        i @ dup 0= IF LEAVE THEN

        i 1 cells + @
        swap
            
        caddr u compare 0= IF 
            i 3 cells + @ 
            i 2 cells + @ 
            -1 LEAVE 
        THEN

    4 cells +LOOP 

    invert IF caddr u THEN
;


: append-with-spaces s" " append-buffer +place append-buffer +place ;
: execute-variable  mapping-operators get-mapping append-with-spaces ;
: execute-string  S\"  S\\\" " append-buffer +place append-buffer +place S\" \"" append-buffer +place ;
: execute-integer append-with-spaces s"  anon_int"  append-buffer +place ;
: execute-store s"  create " append-buffer +place append-buffer +place s"  ," append-buffer +place ;
: execute-comment 2drop ;


create token-rules
rgx-variable-string , 0 , ' execute-variable , \ variable - string variant
rgx-string-single   , 1 , ' execute-string ,   \ string - single quotes
rgx-string-double   , 1 , ' execute-string ,   \ string - double quotes
rgx-integer         , 0 , ' execute-integer ,  \ integer
rgx-comment         , 0 , ' execute-comment ,  \ comment
rgx-store           , 0 , ' execute-store ,    \ : store variables 
rgx-variable-char   , 0 , ' execute-variable , \ variable - char variant
0 ,




: fetch-rule ( addr -- c*n )
    dup 3 cells + swap 
    ?DO 
        i @ 
    1 cells +LOOP
;


: token-matcher { caddr u regexp n func -- func -1 | 0 }

    caddr u regexp match if 

       n get-subex

       func -1 

    else \ regexp did not match
        0 
    then 
;



: get-execute-token ( caddr u --  caddr u exec-token | 0 )

    0 token-rules ?DO

        i @ 0= IF 0 LEAVE THEN

        i fetch-rule

        token-matcher IF LEAVE THEN

    3 cells +LOOP 

;



: execute-token ( caddr u -- caddr1 u1 flag )

 get-execute-token
 
 dup if
    \ special case store operation ':' 
    dup ['] execute-store = if

        drop 2drop              \ we throw away the execute and the string 
        get-execute-token if    \ no match no problem, see reference implementation in ruby ;)

            execute-store

        then
        -1
    \ standard execution
    else
        execute -1
    then

 else 
    drop 0
 then 
;




: golf-preprocess ( caddr u -- caddr1 u1 )

s" " append-buffer place \ reset append buffer

begin 
    execute-token
    while 
repeat  
    2drop

append-buffer count
;

