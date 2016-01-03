
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


\ just the integer value as char in a golf string
: coerce_rawcast_int_to_string ( typed-int -- typed-str )

    val 1 allocate throw dup -rot c! 1
    anon_str
;



: coerce_int_to_block ( typed-int -- typed-block )
    val
    create_int_func anon_block
;



: coerce_rawcast_int_to ( typed typedid -- typed )

    CASE

        typeno_int OF  ENDOF
        typeno_array OF coerce_int_to_array ENDOF
        typeno_str OF  coerce_rawcast_int_to_string ENDOF
        typeno_block OF coerce_int_to_block ENDOF

    ENDCASE 
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

    :noname typeno_str POSTPONE literal POSTPONE coerce_rawcast_to POSTPONE ;

    golf_map_to_array

    ['] golf_+ golf_foldr
;

: coerce_array_to_block ( typed-array -- typed-block )

    :noname typeno_block POSTPONE literal POSTPONE coerce_to POSTPONE ;

    golf_map_to_array

    ['] golf_+ golf_foldr
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
: coerce_str_to_array ( typed-string -- typed array )
    val { addr len } golf_slice_start len 0 
    u+do
        addr i chars + c@ anon_int
    loop 
    anon_array
;


: coerce_str_to_block  ( typed-string -- typed-block )
    val golf-parse anon_block
;

: coerce_str_to ( typed typedid -- typed )

    CASE

        typeno_int OF 1 throw ENDOF
        typeno_array OF coerce_str_to_array ENDOF
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

: coerce_to_impl (  typed typedid -- typed )
    over golf_type CASE
        typeno_int OF coerce_int_to ENDOF
        typeno_array OF coerce_array_to ENDOF
        typeno_str OF coerce_str_to ENDOF
        typeno_block OF coerce_block_to ENDOF
    ENDCASE 
;

: coerce_rawcast_to_impl (  typed typedid -- typed )
    over golf_type CASE
        typeno_int OF coerce_rawcast_int_to ENDOF
        typeno_array OF coerce_array_to ENDOF
        typeno_str OF coerce_str_to ENDOF
        typeno_block OF coerce_block_to ENDOF
    ENDCASE 
;

' coerce_to_impl IS coerce_to
' coerce_rawcast_to_impl IS coerce_rawcast_to


