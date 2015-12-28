
: str-append { addr1 u1 addr2 u2 -- addr u }

    addr1 u1 u2 + dup { u } resize throw { addr }
    addr2 addr u1 + u2 move
    addr u 
;


: composition  { xt1 xt2 -- xt3 }

    :noname xt1 POSTPONE LITERAL POSTPONE execute xt2 POSTPONE LITERAL POSTPONE execute POSTPONE ;

;


