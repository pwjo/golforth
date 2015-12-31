1 constant typeno_int
2 constant typeno_array
3 constant typeno_str
4 constant typeno_block

Defer golf-preprocess ( caddr u -- xt )

20 constant max_array_depth

create slice_start max_array_depth cells allot
create slice_start_idx 0 ,


\ -----------------------------
\ - Projektionen
\ -----------------------------
: golf_type ( ty -- t )
    execute dup  CASE
        typeno_int OF nip ENDOF
        typeno_str OF nip nip ENDOF
        typeno_block OF nip ENDOF
        typeno_array OF nip nip ENDOF
    ENDCASE ;

: val ( xt -- x )
    execute drop ;

: val_dump ( xt -- )
    execute
    CASE
        typeno_int OF int_to_string type ENDOF \ dot makes space
        typeno_str OF type ENDOF
        typeno_block OF . ENDOF
        typeno_array OF s" [" type
            0 u+do dup i cells + @ recurse loop
            drop
            s" ]" type
        ENDOF
    ENDCASE ;

\ -------------------------
\ - Named konstruktoren
\ -------------------------
: ctor_int ( n -- )
    create , typeno_int ,
  does>
    dup @ swap cell+ @ ;

: ctor_str ( addr n -- )
    create swap , , typeno_str ,
  does>
    dup @ swap cell+ dup @ swap cell+ @ ;

: ctor_block ( addr n -- )
    create swap , , typeno_block ,
  does>
    dup @ swap cell+ dup @ swap cell+ @ ;

\ ------------------------
\ - Anonyme konstruktoren
\ ------------------------
: anon_int { u -- typext }
    :noname  u POSTPONE LITERAL POSTPONE typeno_int  POSTPONE ; ;

: anon_str { addr u -- typext }
    :noname  addr POSTPONE LITERAL u POSTPONE LITERAL POSTPONE typeno_str POSTPONE ; ;

: anon_block { xt -- typext }
    :noname  xt POSTPONE LITERAL POSTPONE typeno_block POSTPONE ; ;



\ -------------------------
\ - block functions
\ -------------------------

: create_str_func { addr u -- xt } 
    
    \ cut the quotes and copy
    u 2 chars - allocate throw { addr1 }
    addr 1 chars + addr1 u 2 chars - move

    :noname addr1 POSTPONE literal u 2 - POSTPONE literal POSTPONE anon_str POSTPONE ; 
;

: create_int_func { n -- xt } 

    :noname n POSTPONE literal POSTPONE anon_int POSTPONE ; 
;

: create_store_func { addr -- xt }

    :noname POSTPONE dup addr POSTPONE literal POSTPONE ! POSTPONE ;
;

: create_load_func { addr -- xt }

    :noname addr POSTPONE literal POSTPONE @ POSTPONE ;
;


\ -----------------------
\ - Array zeug
\ ------------------------

: current_slice_start ( -- addr )
    slice_start slice_start_idx @ cells + ;
: active_slice_start ( -- addr )
    slice_start slice_start_idx @ 1- cells + ; ( XXX error handling if <0 )
: inc_slice_start_idx ( -- )
    slice_start_idx dup @ 1+ swap ! ;
: dec_slice_start_idx ( -- )
    slice_start_idx dup @ 1- swap ! ;

: golf_slice_start ( -- )
    slice_start_idx @ max_array_depth < if
        depth current_slice_start !
        inc_slice_start_idx
    else
        abort
    endif ;

: make_array_xt { addr n -- }
    :noname addr POSTPONE LITERAL n POSTPONE LITERAL POSTPONE typeno_array POSTPONE ; ;

: anon_array
    depth active_slice_start @ - dup >r
    dup cells dup  allocate drop
    + swap 0 u+do
        cell - tuck !
    loop r>
    make_array_xt dec_slice_start_idx ;


: golf_array_nth ( arr n -- arr[n] )
    swap val drop swap cells + @ ;

: golf_array_len ( arr -- len )
    val nip ;


\ -----------------------------
\ - Golfscript ~ Operator
\ ----------------------------
: golf_sim_str ( tstr -- )
    val golf-preprocess execute
;

: golf_sim_int ( tu -- typedxt )
    val invert anon_int ;

: golf_sim_array ( tarr -- )
    val 0 u+do
        dup i cells + @ tuck drop
    loop drop ;

: golf_sim_block ( block -- )
    val execute
;

: golf_sim ( typed -- ... )

    dup golf_type CASE
        typeno_int OF golf_sim_int ENDOF
        typeno_str OF  golf_sim_str ENDOF
        typeno_block OF golf_sim_block ENDOF
        typeno_array OF golf_sim_array ENDOF
    ENDCASE ;



\ ------------------------------
\ array/string iteration words
\ ------------------------------
: golf_foldr { arr xt -- varies } arr golf_sim arr golf_array_len 1 u+do xt execute loop ;
: golf_foldl { arr xt -- varies } arr 0 golf_array_nth arr golf_array_len 1 u+do arr i golf_array_nth xt execute loop ; 

: golf_each { arr xt -- varies } arr golf_array_len 0 u+do arr i golf_array_nth xt execute loop ; 
: golf_each_reverse { arr xt -- varies } arr golf_sim arr golf_array_len 0 u+do xt execute loop ;

: golf_iterate { arr xt -- varies } arr golf_array_len 0 u+do arr i golf_array_nth i xt execute loop ; 
: golf_iterate_reverse { arr xt -- varies } arr golf_sim arr golf_array_len 0 u+do i xt execute loop ;



: create_array_transform_store_func { store-addr transform-xt increment-xt -- }

  :noname POSTPONE swap transform-xt POSTPONE literal POSTPONE execute POSTPONE swap \ transform
          store-addr POSTPONE literal POSTPONE swap 
          increment-xt POSTPONE literal POSTPONE execute POSTPONE +  \ target address
          POSTPONE ! POSTPONE ; \ store
;

: golf_map_raw { arr xt increment-xt -- varies } 

    arr golf_array_len { n } n allocate throw  { store-arr } 

    store-arr xt increment-xt create_array_transform_store_func { store-xt }
    arr store-xt golf_iterate
    store-arr n 
;

: golf_map_to_array ( arr xt -- varies ) 

    ['] cells 
    golf_map_raw
    make_array_xt
;

: golf_map_to_string ( arr xt -- varies ) 

    ['] chars 
    golf_map_raw
    anon_str
;


\ test:
\ golf_slice_start 65 anon_int 68 anon_int anon_array ' coerce_int_to_string_raw golf_map_to_array val_dump
\ golf_slice_start 65 anon_int 68 anon_int anon_array ' val golf_map_to_string val_dump



\ -------------------------
\ - type coercion helpers
\ -------------------------
Defer coerce_to  (  typed typedid -- typed )
Defer coerce_rawcast_to  (  typed typedid -- typed )


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




\ --------------------------------
\ - Golfscipt + Operator
\ -------------------------------
: golf_+_int ( ty1 ty2 -- tyo )
    val swap val + anon_int ;

: golf_+_array { ty1 ty2 -- tyo }
    golf_slice_start
    ty1 golf_sim ty2 golf_sim anon_array ;

: golf_+_str { ty1 ty2 -- tyo }
    ty1 val ty2 val 
    str-append anon_str
;

: golf_+_block { ty1 ty2 -- tyo }
    ty1 val ty2 val 
    composition anon_block
;

: golf_+ ( ty1 ty2 -- tyo )

    2op_coerce_to_max CASE
        typeno_int OF golf_+_int ENDOF
        typeno_array OF golf_+_array ENDOF
        typeno_str OF golf_+_str ENDOF
        typeno_block OF golf_+_block ENDOF
    ENDCASE 
;

\ --------------------------------
\ - Golfscipt = Operator
\ -------------------------------

\ *_equal implements the raw = functionality between
\ two values of the same type

: golf_equal_int ( ty1 ty2 -- flag )
    val swap val =
;

Defer golf_equal

: golf_equal_array ( ty1 ty2 -- flag )

    2dup golf_array_len
    swap golf_array_len

    <> if 2drop 0 EXIT then

    val { addr1 len }
    val drop { addr2 }
    
    len 0 u+do
        addr1 i cells + @  
        addr2 i cells + @  

        golf_equal invert if
            0 UNLOOP EXIT
        then
    loop
 
    -1
;

: golf_equal_str ( ty1 ty2 -- flag )
    val rot val
    compare
    0= if
    -1
    else 
        0
    then
;


: golf_equal_impl ( ty1 ty2 - flag )

    \ different types means we are not equal
    2dup golf_type 
    swap golf_type 
    <> if 0 EXIT then

    dup golf_type
    CASE
        typeno_int OF golf_equal_int ENDOF
        typeno_array OF golf_equal_array ENDOF
        typeno_str OF golf_equal_str ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 

;

' golf_equal_impl IS golf_equal

: golf_=

    \ TODO: implement the index functionality for different
    \       types
    golf_equal 
    if
        1 anon_int
    else
        0 anon_int
    then 
;

\ --------------------------------
\ - Golfscipt - Operator
\ -------------------------------
: golf_-_int { ty1 ty2 -- tyo }
    ty1 val ty2 val - anon_int 
;

: golf_-_array { ty1 ty2 -- tyo }
    1 throw \ TODO
;


: golf_- ( ty1 ty2 -- tyo )
    2op_coerce_to_max CASE
        typeno_int OF golf_-_int ENDOF
        typeno_array OF golf_-_array ENDOF
        typeno_str OF 1 throw ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE ;

\ --------------------------------
\ - Golfscipt % Operator
\ -------------------------------
: golf_%_int { ty1 ty2 -- tyo }
    ty1 val ty2 val mod anon_int ;

: golf_% ( ty1 ty2 -- tyo )
    dup golf_type CASE
        typeno_int OF golf_%_int ENDOF
    ENDCASE ;


\ --------------------------------
\ - Golfscript ) Operator
\ --------------------------------
\ increment number
: golf_)_int ( tyn -- tyn+1 )
    val 1+ anon_int ;

\ XXX missing handling of special cases (array size 0 or 1)
: golf_)_array ( array -- front last )
    golf_slice_start
    dup val 1- 0 u+do
        dup i cells + @ swap
    loop drop
    anon_array swap
    val 1- cells + @ ;

: golf_)
     dup golf_type CASE
         typeno_int OF golf_)_int ENDOF
         typeno_array OF golf_)_array ENDOF
     ENDCASE ;

\ -----------------------------
\ - Golfscript stack operators
\ ----------------------------
: golf_.  dup ;
: golf_;  drop ;
: golf_backslash  swap ;
: golf_@  rot ;


\ --------------------------------
\ - Golfscript loop constructs
\ --------------------------------
 : golf_do { tyblock -- .. }
    BEGIN
        tyblock golf_sim
        val
    WHILE 
    REPEAT 
;

s" golf_coercion.fs" included

\ ----------------------------
\ - Zeug
\ Translate following code:
\ ;'2706 410'
\ ~{.@\%.}do;

\ 0 anon_int golf_; s" 2706 410" anon_str golf_sim s" .@\%" anon_block golf_do golf_;


\ -------------------------
\ -  "Tests"
\ ------------------------
: test_golf_@
    1 anon_int 2 anon_int s" three " anon_str 4 anon_int
    golf_@
    val . val . val type val . ;

( [1 3 5][10 32]+ -> [1 3 5 10 32] )
: test_golf_+_array
    golf_slice_start 1 anon_int 3 anon_int  5 anon_int anon_array
    golf_slice_start 10 anon_int  32 anon_int  anon_array
    golf_+ golf_sim
    val . val . val . val . val . ;

( [3 8]~~+ )
: test_golf_+_int
    golf_slice_start 3 anon_int 8 anon_int anon_array
    golf_sim golf_sim golf_+
    val . ;
