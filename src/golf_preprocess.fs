s" regex/regex.fth" included

S\" ^[a-zA-Z_][a-zA-Z0-9_]*" regex$ constant rgx-variable-string
S\" ^'((?:\\\\.|[^'])*)'?" regex$ constant rgx-string-single
S\" ^\"((?:\\\\.|[^\"])*)\"?" regex$ constant rgx-string-double
S\" ^-?[0-9]+" regex$ constant rgx-integer
S\" ^#[^\\n\\r]*" regex$ constant rgx-comment
S\" ^:" regex$ constant rgx-store
S\" ^\\{" regex$ constant rgx-block-start
S\" ^\\}" regex$ constant rgx-block-end
S\" ^." regex$ constant rgx-variable-char


create mapping-operators
s" ~" , , s" golf_sim" , ,
s" +" , , s" golf_+" , ,
0 ,



: str-append { addr1 u1 addr2 u2 -- addr u }
addr1 u1 u2 + dup { u } resize throw { addr }
addr2 addr u1 + u2 move
addr u ;


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



\ standard signature ( buffer buffer-len addr u  -- )
: append-with-spaces { buffer buffer-len addr u } buffer buffer-len s"  " str-append addr u str-append ;

: execute-variable  mapping-operators get-mapping append-with-spaces ;

: execute-string  { buf buf-len addr u } buf buf-len S\"  S\\\" " str-append addr u str-append S\" \" anon_str " str-append ;
: execute-integer ( buf buf-len addr u -- adr1 u1)  str-append s"  anon_int"  str-append ;
: execute-store   { buf buf-len addr u }  buf buf-len s"  create " str-append addr u str-append s"  ," str-append ;
: execute-comment 2drop ;
: execute-block-start 2drop ;
: execute-block-end 2drop ;



create token-rules
rgx-variable-string , 0 , ' execute-variable , \ variable - string variant
rgx-string-single   , 1 , ' execute-string ,   \ string - single quotes
rgx-string-double   , 1 , ' execute-string ,   \ string - double quotes
rgx-integer         , 0 , ' execute-integer ,  \ integer
rgx-comment         , 0 , ' execute-comment ,  \ comment
rgx-store           , 0 , ' execute-store ,    \ : store variables 
rgx-block-start     , 0 , ' execute-block-start ,    \ block treatment
rgx-block-end       , 0 , ' execute-block-end ,  
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



: execute-token { caddr u buffer buffer-len -- caddr1 u1 append-addr1 append-u1 flag }

    caddr u

    get-execute-token

    \ exit if nothing was found
    dup 0= if drop buffer buffer-len 0 EXIT then

    \ standard execute stack:
    \ ( buffer buffer-len addr u  -- )
    CASE 
    
        \ 
        \ special case: store operation ':' 
        \ 
        ['] execute-store OF
            2drop              \ we throw away the execute and the string 
            get-execute-token if    \ no match no problem, see reference implementation in ruby ;)

                buffer execute-store
            then

            -1
        ENDOF
          
        \ 
        \ special case: block start '{' 
        \ 
        ['] execute-block-start OF
            2drop

            4096 chars allocate 

            begin
                recurse dup
                -2 = if drop 0 then
            while
            repeat

            buffer 
            buffer-len 

            S\" S\\\" " str-append

            2swap str-append

            S\" \" anon_block" str-append

            -1
        ENDOF

        
        ['] execute-block-end OF
            2drop
            buffer buffer-len
            -2
        ENDOF

    \ 
    \ standard execution
    \ 
    { addr u xt }
    buffer buffer-len addr u xt 

    execute -1
    0 \ this is a dummy for drop in the endcase
    ENDCASE 

;


: golf-preprocess ( caddr u -- caddr1 u1 )

4096 chars allocate \ start buffer

begin 
    execute-token
    while 
repeat  
    rot drop
    rot drop


;

