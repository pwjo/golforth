
: str-append { addr1 u1 addr2 u2 -- addr u }
    \ damger together with dup ;)
    \ addr1 u1 u2 + dup { u } resize throw { addr }
    u1 u2 + dup { u } allocate throw { addr }
    addr1 addr u1 move
    addr2 addr u1 + u2 move
    addr u 
;


: str_to_heap { addr u -- addr1 u }

    u allocate throw { addr1 }
    addr addr1 u move

    addr1 u
;


: composition  { xt1 xt2 -- xt3 }

    :noname xt1 POSTPONE LITERAL POSTPONE execute xt2 POSTPONE LITERAL POSTPONE execute POSTPONE ;

;


: int_to_string ( d -- addr u )

    BASE @ >r

    dup >r \ keep for sign
    abs
    DECIMAL 0
    <# 
    #S 
    r> SIGN
    #>

    r> BASE !
;
