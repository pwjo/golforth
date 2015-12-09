
\ broken with eval
wordlist constant golf-wordlist

\ get-order golf-wordlist swap 1+ set-order 

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


: get-mapping { caddr u map-table --  0 | caddr1 u1 }

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

    invert IF 0 THEN
;


: create-variable { addr u -- }

        s" create " dup u + chars allocate  
        2swap str-append 
        addr u str-append

        get-current { w } 
        golf-wordlist set-current
        evaluate 
        w set-current 
;


: append-with-spaces { buffer buffer-len addr u } buffer buffer-len s"  " str-append addr u str-append ;

: execute-op-or-var  mapping-operators get-mapping dup if append-with-spaces else drop then ;

: execute-string  { buf buf-len addr u } buf buf-len S\"  S\\\" " str-append addr u str-append S\" \" anon_str " str-append ;
: execute-integer ( buf buf-len addr u -- adr1 u1)  append-with-spaces s"  anon_int"  str-append ;


: execute-variable-use  ( buf buf-len addr u ) append-with-spaces ;

: execute-store   { buf buf-len addr u }  

    \ check for variable existence, 
    \ and register if not in wordlist
    addr u golf-wordlist search-wordlist 0= if
    \ addr u find-name 0= if
        addr u create-variable 
    else 
        drop
    then 

    \ the we execute the store, but we also put it on the stack
    buf buf-len s"  dup " str-append addr u append-with-spaces s"  ," str-append 

;

: execute-comment       2drop ;
: execute-block-start   2drop ;
: execute-block-end     2drop ;



create token-rules
rgx-variable-string , 0 , ' execute-op-or-var , \ variable - string variant
rgx-string-single   , 1 , ' execute-string ,   \ string - single quotes
rgx-string-double   , 1 , ' execute-string ,   \ string - double quotes
rgx-integer         , 0 , ' execute-integer ,  \ integer
rgx-comment         , 0 , ' execute-comment ,  \ comment
rgx-store           , 0 , ' execute-store ,    \ : store variables 
rgx-block-start     , 0 , ' execute-block-start ,    \ block treatment
rgx-block-end       , 0 , ' execute-block-end ,  
rgx-store           , 0 , ' execute-store ,    \ : store variables 
rgx-variable-char   , 0 , ' execute-op-or-var , \ variable - char variant
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
    CASE 
    
        \ 
        \ special case: store operation ':' 
        \ 
        ['] execute-store OF
            2drop              \ we throw away the string  ':'
            get-execute-token if    \ no match no problem, see reference implementation in ruby ;)

                buffer buffer-len 2swap 
                execute-store
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

            buffer buffer-len 
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
    \ standard token execution (everyring but '{' '}' or ':'
    \ 
    { addr u xt }

    
    \ first we have to check if we are a variable
     addr u golf-wordlist search-wordlist  \ notice that we are using find-name instead of find becuase
     \ addr u find-name  \ notice that we are using find-name instead of find becuase
                          \ we don't need a counted string in mem for that, if you have
                          \ portability issues, you can easily rewrite this
    if drop


        \ for now we still exclude operators
\        addr u mapping-operators get-mapping  \ 
\        dup if 2drop
\            buffer buffer-len addr u xt  \ 
\            execute \ 
\        else drop \ 

            buffer buffer-len addr u 
            execute-variable-use 
\        then  \ 
    else                          

        buffer buffer-len addr u xt 
        execute
    then 
    -1
            
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

