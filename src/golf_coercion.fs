
\ -------------------------
\ integer coercion
\ -------------------------
: coerce_int_to_array ( typed-int -- typed-array )

    1 allocate throw dup -rot !
    1 make_array_xt 
;

: coerce_int_to_string ( typed-int -- typed-str )

    val int_to_string  
    str_to_heap anon_str
;


\ just the integer value as char
: coerce_int_to_string_raw ( typed-int -- typed-str )

    val 1 allocate throw dup -rot c! 1
    anon_str
;

: coerce_int_to_block ( typed-int -- typed-block )
    val
    create_int_func anon_block
;

: coerce_int_to ( typed typedid -- typed )

    CASE

        typeno_int OF  ENDOF
        typeno_array OF coerce_int_to_array ENDOF
        typeno_str OF  coerce_int_to_string ENDOF
        typeno_block OF coerce_int_to_block ENDOF

    ENDCASE 
;



\ -------------------------
\ array coercion
\ -------------------------

: coerce_array_to_str ( typed-array -- typed )
    \ TODO: use fold for that
    \       convert each element to a string and concatenate them (golf_+)
    1 throw
;

: coerce_array_to_block ( typed-array -- typed-block )
    \ TODO: use fold for that
    \       convert each element to a block and make a composition (golf_+)
    1 throw
;

: coerce_array_to ( typed typedid -- typed )

    CASE

        typeno_int OF 1 throw ENDOF
        typeno_array OF ENDOF
        typeno_str OF coerce_array_to_str ENDOF
        typeno_block OF coerce_array_to_block ENDOF

    ENDCASE 
;


\ -------------------------
\ string coercion
\ -------------------------

: coerce_str_to_block  ( typed-string -- typed-block )
    val golf-preprocess anon_block
;

: coerce_str_to ( typed typedid -- typed )

    CASE

        typeno_int OF 1 throw ENDOF
        typeno_array OF 1 throw ENDOF
        typeno_str OF   ENDOF
        typeno_block OF coerce_str_to_block ENDOF

    ENDCASE 
;


\ -------------------------
\ block coercion
\ -------------------------


: coerce_block_to ( typed typedid -- typed )

    CASE

        typeno_int OF 1 throw ENDOF
        typeno_array OF 1 throw ENDOF
        typeno_str OF  1 throw  ENDOF
        typeno_block OF ENDOF

    ENDCASE 
;


\ -------------------------
\ typed coercion
\ -------------------------

: coerce_to (  typed typedid -- typed )
    over golf_type CASE
        typeno_int OF coerce_int_to ENDOF
        typeno_array OF coerce_array_to ENDOF
        typeno_str OF coerce_str_to ENDOF
        typeno_block OF coerce_block_to ENDOF
    ENDCASE 
;


\ -------------------------
\ - type coercion helpers
\ -------------------------
: 2op_max_type ( ty1 ty2 -- max-type-id)

    golf_type swap golf_type
    2dup < if
        nip
    else
        drop
    then
;

: 2op_coerce_to_max ( ty1 ty2 -- ty3 ty4 max-type )
    swap 2dup 2op_max_type { maxt } 
    maxt coerce_to 
    swap
    maxt coerce_to
    maxt
;

