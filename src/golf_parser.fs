wordlist constant golf-wordlist


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

\ complete 
s" ~" , , ' golf_sim ,
s" ." , , ' golf_. ,
s" ;" , , ' golf_; ,
s" \" , , ' golf_backslash ,
s" @" , , ' golf_@ ,

s" do" , , ' golf_do ,
s" while" , , ' golf_while ,
s" until" , , ' golf_until ,
s" if" , , ' golf_if ,

s" [" , , ' golf_slice_start ,
s" ]" , , ' anon_array ,
s" (" , , ' golf_( ,
s" ?" , , ' golf_? ,
s" ," , , ' golf_, ,

s" +" , , ' golf_+ ,

s" print" , , ' golf_print ,
s" puts" , , ' golf_puts ,
s" n" , , ' golf_n ,
s" abs" , , ' golf_abs ,
s" base" , , ' golf_base ,
s" zip" , , ' golf_zip ,

\ done with functionality we will not implement
s" =" , , ' golf_= , \ block index function
s" -" , , ' golf_- , \ block filter function

\ incomplete
s" !" , , ' golf_! ,
s" )" , , ' golf_) ,

s" %" , , ' golf_% ,

0 ,




: get-mapping { caddr u map-table --  0 | xt }

    0 map-table ?DO
        
        i @ dup 0= IF LEAVE THEN

        i 1 cells + @
        swap
            
        caddr u compare 0= IF 
            i 2 cells + @ 
            -1 LEAVE 
        THEN

    3 cells +LOOP 

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


: execute-op-or-var  

    mapping-operators get-mapping 
    dup if 
        composition
    else 
        drop 
    then 
;



: execute-string  ( xt1 addr u -- xt2 ) 

    create_str_func composition
;


: execute-integer ( xt1 addr u -- xt2 )  

    s>number? 
    nip
    0=  if 
        s" failed number conversion" exception throw 
    then 
 
    create_int_func composition
;


: execute-variable-use  ( xt1 variable-address -- xt2 ) 

    create_load_func

    composition

;


: execute-store { xt addr u -- xt1 }  

    \ check for variable existence, 
    \ and register if not in wordlist
    addr u golf-wordlist search-wordlist 0= if
        addr u create-variable 
        xt addr u recurse 
    else 
        create_store_func 
        xt swap composition
    then 

;

: execute-comment       2drop ;
: execute-block-start   2drop ;

: execute-block-end { xt1 xt-block -- xt3 }  

    xt1 
    :noname xt-block POSTPONE literal POSTPONE anon_block POSTPONE ; 

    composition
;


create token-rules
rgx-variable-string , 0 , ' execute-op-or-var , \ variable - string variant
rgx-string-single   , 0 , ' execute-string ,    \ string - single quotes
rgx-string-double   , 0 , ' execute-string ,    \ string - double quotes
rgx-integer         , 0 , ' execute-integer ,   \ integer
rgx-comment         , 0 , ' execute-comment ,   \ comment
rgx-store           , 0 , ' execute-store ,     \ : store variables 
rgx-block-start     , 0 , ' execute-block-start ,  \ block treatment
rgx-block-end       , 0 , ' execute-block-end ,  
rgx-store           , 0 , ' execute-store ,     \ : store variables 
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


Defer execute-token ( caddr u xt -- caddr1 u1 xt1 flag )


: collect-block-token { xt -- caddr1 u1 xt1 }

    :noname POSTPONE ;

    begin
        execute-token dup
        -2 = if drop 0 then
    while
    repeat

    xt swap 
    execute-block-end
;


: collect-store-token { caddr u xt -- xt }

    caddr u 
    get-execute-token if    \ no match no problem, see reference implementation in ruby ;)
        xt -rot
        execute-store
    then

;

\ standard token execution (everyring but '{' '}' or ':'
: standard-token { addr-token u-token xt-token xt  --  caddr1 u1 xt1 flag }
    
    \ first we have to check if we are a variable
    addr-token u-token golf-wordlist search-wordlist 
    if  xt swap
        execute-variable-use 

    else                          
        xt addr-token u-token xt-token
        execute
    then 

;


\ parsing string in caddr u and attaching it to xt
: execute-token-impl { caddr u xt -- caddr1 u1 xt1 flag }

    caddr u get-execute-token

    \ exit if nothing was found
    dup 0= if drop xt 0 EXIT then

    ( caddr1 u1 xt1 -- )
    CASE 
    
        \ special case: store operation ':' 
        ['] execute-store OF
            2drop              \ we throw away the string  ':'
            xt collect-store-token
            -1
        ENDOF
          
        \ special case: block start '{' 
        ['] execute-block-start OF
            2drop  
            xt collect-block-token 
            -1
        ENDOF

        
        \ special case: block end '}' 
        ['] execute-block-end OF
            2drop 
            xt 
            -2
        ENDOF

        \ standard token execution (everyring but '{' '}' or ':'
            xt standard-token
            -1

    0 \ this is a dummy for drop in the endcase
    ENDCASE 

;


' execute-token-impl IS execute-token



: golf-parse-impl ( caddr u -- xt )

    :noname POSTPONE ;

    begin 
        execute-token
        while 
    repeat  
    
    nip nip 
;

' golf-parse-impl IS golf-parse
