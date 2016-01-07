1 constant typeno_int
2 constant typeno_array
3 constant typeno_str
4 constant typeno_block

Defer golf-parse ( caddr u -- xt )
Defer golf_equal ( ty1 ty2 - flag )
Defer golf_sim ( typed -- ... )
Defer golf_% ( ty1 ty2 -- tyo )


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


\ -----------------------------
\ array operators and helpers
\ -----------------------------

(        active_slice_start dup @ r> + swap ! )

: current_slice_start ( -- addr )
    slice_start slice_start_idx @ cells + ;
: active_slice_start ( -- addr )
    slice_start slice_start_idx @ 1- cells + ; ( XXX error handling if <0 )
: inc_slice_start_idx ( -- )
    slice_start_idx dup @ 1+ swap ! ;
: dec_slice_start_idx ( -- )
    slice_start_idx dup @ 1- swap ! ;

: move_slice_start { by idx -- }
    slice_start idx cells + dup @ by + swap ! ;

: shift_down_slice_start { n -- }
    depth
    0 slice_start_idx @ 1- do
        dup slice_start i cells + @ - n - dup
        0< IF
            i move_slice_start
        ELSE
            drop  LEAVE
        ENDIF
    -1 +loop drop ;

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


: anon_array_reverse
    depth active_slice_start @ - dup >r
    dup cells allocate drop dup >r
    swap 0 u+do
        tuck ! cell +
    loop drop r> r>
    make_array_xt dec_slice_start_idx ;


: golf_array_nth ( arr n -- arr[n] )
    swap val drop swap cells + @ ;

: golf_array_len ( arr -- len )
    val nip ;


: golf_make_empty_array ( -- typed-arr )
    golf_slice_start 
    anon_array
;


\ returns a subsection of an array
\ if u1 is outside of array you will get an empty array
\ if u2 is outside you will get everything until the end 
\ of arr1
: golf_array_slice { typed-arr1 u1 u2 -- typed-arr2 }

     u1 u2 > if
        golf_make_empty_array
        EXIT
    then

    \ check u1 bounds
    typed-arr1 golf_array_len 1- 
    dup u1 < if 
        drop
        golf_make_empty_array
        EXIT
    then

    \ check u2 bounds
    dup u2 > if 
        drop u2     
    then 1+
    { limit }

    golf_slice_start
    limit u1 ?do
        typed-arr1 i golf_array_nth
    loop
    anon_array
;


: golf_array_match_at { typed-arr1 u1 typed-arr2 -- flag }

    typed-arr1 u1 
    typed-arr2 golf_array_len 1- u1 + \ second index
    
    golf_array_slice typed-arr2 golf_equal
;


\ look for arr2 in arr1 starting at index u1
\ if arr2 has been found, the index in arr1 is returned
: golf_array_search { typed-arr1 u1 typed-arr2 -- u2 -1 | 0 } 

    typed-arr1 golf_array_len u1 ?do 
        typed-arr1 i typed-arr2 golf_array_match_at 
        if
            i -1 UNLOOP EXIT
        then
    loop

    0
;

: golf_array_append { arr1 typed -- arr2 }
   golf_slice_start
        arr1 golf_sim
        typed
    anon_array
;


\ returns false if index out of bounds,
\ last index if index=-1
: golf_array_index_bounds_check ( array_len typed-index -- index -1 | 0 )  

    val
    
    \ specal case -1 = array_len -1
\    dup -1 = if
\        drop 1-  
    dup 0< if
        + dup 0< if drop 0 EXIT then
    else
        \ bigger then array, then we are empty
        2dup <= if 2drop 0 EXIT then
        nip
    then

    -1
;
\ -------------------------------
\ - Golfscript ! Operator
\ -------------------------------

: golf_!_int ( int -- int )
    val 0= IF 1 ELSE 0 ENDIF anon_int ;

: golf_!_length ( array/string -- int )
    val nip 0= IF 1 ELSE 0 ENDIF anon_int ;

: golf_! ( varies - int )
    dup golf_type CASE
        typeno_int OF golf_!_int ENDOF
        typeno_array OF golf_!_length ENDOF
        typeno_str OF golf_!_length ENDOF
        typeno_block OF 0 ENDOF ( Implement? )
    ENDCASE ;



\ -----------------------------
\ boolean helpers
\ -----------------------------

: flag_to_golf_boolean ( flag -- typed-int )

    if 1 anon_int 
    else 0 anon_int 
    then 
;

: golf_boolean_to_flag ( typed -- flag )

    golf_! val 0=
;


\ -----------------------------
\ - Golfscript ~ Operator
\ -----------------------------
: golf_sim_str ( tstr -- )
    val golf-parse execute
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

: golf_sim_impl ( typed -- ... )

    dup golf_type CASE
        typeno_int OF golf_sim_int ENDOF
        typeno_str OF  golf_sim_str ENDOF
        typeno_block OF golf_sim_block ENDOF
        typeno_array OF golf_sim_array ENDOF
    ENDCASE ;

' golf_sim_impl IS golf_sim

\ ------------------------------
\ array/string iteration words
\ ------------------------------
: golf_foldr { arr xt -- varies } 

    arr golf_sim arr golf_array_len 1 u+do xt execute loop ;

: golf_foldl { arr xt -- varies } 

    arr 0 golf_array_nth arr golf_array_len 1 u+do arr i golf_array_nth xt execute loop ; 

: golf_each { arr xt -- varies } 

    arr golf_array_len 0 u+do arr i golf_array_nth xt execute loop ; 

: golf_each_reverse { arr xt -- varies } 

    arr golf_sim arr golf_array_len 0 u+do xt execute loop ;

: golf_iterate { arr xt -- varies } 

    arr golf_array_len 0 u+do arr i golf_array_nth i xt execute loop ; 

: golf_iterate_reverse { arr xt -- varies } 

    arr golf_sim arr golf_array_len 0 u+do i xt execute loop ;



: create_array_transform_store_func { store-addr transform-xt increment-xt -- }

  :noname POSTPONE swap transform-xt POSTPONE literal POSTPONE execute POSTPONE swap \ transform
          store-addr POSTPONE literal POSTPONE swap 
          increment-xt POSTPONE literal POSTPONE execute POSTPONE +  \ target address
          POSTPONE ! POSTPONE ; \ store
;

: golf_map_raw { arr xt increment-xt -- varies } 

    arr golf_array_len { n } n increment-xt execute allocate throw  { store-arr } 

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



\ ------------------------------------
\ type coercion and operator helpers
\ ------------------------------------
Defer coerce_to  (  typed typedid -- typed )
Defer coerce_rawcast_to  (  typed typedid -- typed )


: 2op_max_type ( ty1 ty2 -- max-type-id)

    golf_type swap golf_type
    max
;

: 2op_min_type ( ty1 ty2 -- min-type-id)

    golf_type swap golf_type
    min
;

: 2op_same_type ( ty1 ty2 -- flag )

    golf_type swap golf_type
    = 
;


\ orders arguments ascending according to their type:
\ int - array - string - block
: 2op_type_order ( ty1 ty2 -- ty1 ty2 | ty2 ty1 )

    2dup golf_type 
    swap golf_type
    < if swap then
;

: 2op_coerce_to_max ( ty1 ty2 -- ty3 ty4 max-type )
    swap 2dup 2op_max_type { maxt } 
    maxt coerce_to 
    swap
    maxt coerce_to
    maxt
;


: 1op_array_string_wrapper { typed-str typed-str xt -- typed-str }

    typed-str typeno_array coerce_to
    xt execute 
    typeno_str coerce_to
;

: 2op_array_string_wrapper { typed-str1 typed-str2 xt -- typed-str }

    typed-str1 typeno_array coerce_to
    typed-str2 typeno_array coerce_to
    xt execute 
    typeno_str coerce_to
;
: golf_array_based_operator { typed-compound xt -- varies }

    typed-compound golf_type CASE
        typeno_array OF typed-compound xt execute ENDOF
        typeno_str OF typed-compound xt 1op_array_string_wrapper ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE

;
\ --------------------------------
\ Golfscipt < > Operators
\ -------------------------------


\ 
\ golf_< compare functionality
\ 
: golf_xt_compare_int ( typed-int typed-int xt-- typed-int )

    -rot
    val swap val swap
    rot
    execute
    flag_to_golf_boolean
;


Defer golf_xt_compare

: golf_xt_compare_array { typed-arr1 typed-arr2 xt -- typed-int }

    typed-arr1 golf_array_len
    typed-arr2 golf_array_len

    min 

    0 u+do
        typed-arr1 i golf_array_nth
        typed-arr2 i golf_array_nth

        xt execute golf_boolean_to_flag if
            1 anon_int UNLOOP EXIT
        then
    loop

    typed-arr1 golf_array_len anon_int
    typed-arr2 golf_array_len anon_int

    xt execute
;

: golf_xt_compare_impl { ty1 ty2 xt-bin -- typed-int }

    ty1 ty2
    2op_coerce_to_max CASE

        typeno_int OF xt-bin golf_xt_compare_int ENDOF
        typeno_array OF :noname xt-bin POSTPONE literal POSTPONE golf_xt_compare POSTPONE ;
                        golf_xt_compare_array ENDOF

        typeno_str OF  :noname xt-bin POSTPONE literal POSTPONE golf_xt_compare POSTPONE ; { xt-next } 
                       :noname xt-next POSTPONE literal POSTPONE golf_xt_compare_array POSTPONE ;
                       2op_array_string_wrapper ENDOF
        1 throw
    ENDCASE
;

' golf_xt_compare_impl IS golf_xt_compare

\ 
\ golf_<> index functionality
\ 

: golf_<>_pivot_index { typed-int typed-arr -- u }

    typed-arr golf_array_len typed-int
    golf_array_index_bounds_check invert if
        typed-int val 0< if 
           0 
        else 
            typed-arr golf_array_len       
        then
    then
;

: golf_<_index_arr ( typed-int typed-arr -- typed-arr )

    dup -rot
    golf_<>_pivot_index 1-
    0 swap
    golf_array_slice
;

: golf_>_index_arr ( typed-int typed-arr -- typed-arr )

    dup -rot
    golf_<>_pivot_index 
    over golf_array_len
    golf_array_slice
;


: golf_<> { ty1 ty2 xt-bin xt-index -- tyo }

    \ if we hace compound and integer we hace index funtionality
    ty1 ty2 2op_same_type invert 
    ty1 ty2 2op_type_order 
              drop golf_type typeno_int = 
    and if
        ty1 ty2 2op_type_order 
        xt-index golf_array_based_operator
        EXIT
    then

    ty1 ty2 xt-bin golf_xt_compare
;

: golf_< ( ty1 ty2 -- tyo )

    ['] < 
    ['] golf_<_index_arr
    golf_<>
;

: golf_> ( ty1 ty2 -- tyo )

    ['] > 
    ['] golf_>_index_arr
    golf_<>
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
\ Golfscipt = Operator
\ -------------------------------

\ *_equal implements the raw = functionality between
\ two values of the same type

: golf_equal_int ( ty1 ty2 -- flag )
    val swap val =
;


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

    2op_coerce_to_max 

    CASE
        typeno_int OF golf_equal_int ENDOF
        typeno_array OF golf_equal_array ENDOF
        typeno_str OF golf_equal_str ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 
;

' golf_equal_impl IS golf_equal






\ see golf_index
: golf_index_array ( typed-int typed-array -- ty )

    dup golf_array_len rot 

    golf_array_index_bounds_check if
        golf_array_nth 
    else 
        drop
    then
;


\ see golf_index
: golf_index_str ( typed-int typed-str -- typed-int )

    dup val nip rot 

    golf_array_index_bounds_check if
        swap val drop swap chars + c@  anon_int
    else 
        drop
    then
;
 
\ one of the ops has to be an integer
\ selects the element with the respective index
\ nothing if index out of bounds
: golf_index ( ty1 ty2 -- ty3 | <empty>)

    2op_type_order 
    dup golf_type 
    CASE
        typeno_array OF golf_index_array ENDOF
        typeno_str OF golf_index_str ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 
;



: golf_= { ty1 ty2 -- typed-int }

    \ if not one of the args is an int we try coercion
    ty1 ty2 2op_same_type
    ty1 ty2 2op_min_type typeno_int >
    or if
        ty1 ty2 golf_equal 
        flag_to_golf_boolean

    \ index operation
    else
        ty1 ty2 golf_index
    then
;


\ --------------------------------
\ Golfscipt logical | ^ & Operators
\ -------------------------------
: golf_logical_bitwise ( typed-int typed-int xt -- typed int )

    -rot
    val swap val 
    rot execute
    anon_int
    
;

: golf_logical ( ty1 ty2 xt -- tyo )

    -rot
    2op_coerce_to_max CASE
        typeno_int OF rot golf_logical_bitwise ENDOF
        typeno_array OF 1 throw ENDOF
        typeno_str OF 1 throw ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 
;

: golf_| ['] or golf_logical ;
: golf_& ['] and golf_logical ;
: golf_^ ['] xor golf_logical ;

\ --------------------------------
\ Golfscipt - Operator
\ -------------------------------
: golf_-_int { ty1 ty2 -- tyo }
    ty1 val ty2 val - anon_int 
;


: equal_arg_xt { typed -- xt }

  :noname typed POSTPONE literal POSTPONE golf_equal POSTPONE or POSTPONE ;
;


: golf_-_array { array filter-array -- tyo }

\ 0 golf_slice_start 2 anon_int 4 anon_int anon_array 2 anon_int equal_arg_xt golf_each 
    array golf_sim_array

    \ we always hide the collecting array behind the last element of the stack
    golf_slice_start anon_array
    swap
    array golf_array_len 0 u+do
        dup equal_arg_xt
        0 filter-array rot golf_each 
        invert if swap golf_+ else drop then
        \ again hide the collecting array
        i array golf_array_len 1- < if swap then
    loop

;

: golf_-_string ( string filter-string -- tyo )

    typeno_array coerce_to
    swap
    typeno_array coerce_to
    swap

    golf_-_array
    typeno_str coerce_to
;

: golf_- ( ty1 ty2 -- tyo )
    2op_coerce_to_max CASE
        typeno_int OF golf_-_int ENDOF
        typeno_array OF golf_-_array ENDOF
        typeno_str OF golf_-_string ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE ;



\ --------------------------------
\ Golfscipt / Operator
\ -------------------------------

\ 
\ math functionality
\ 
: golf_/_int_int ( ty1 ty2 -- tyo )
    val swap val swap
    / anon_int 
;

\ 
\ split functionality
\ 

: golf_/_split_arr_arr { base-arr search-arr -- tyo }
    
    \ empty array crashes ruby implementation

    search-arr golf_array_len { search-arr-len }
    golf_make_empty_array
    0 
    
    begin { result-arr last-index }

        base-arr last-index search-arr golf_array_search 
    
    while { new-index }

        base-arr last-index new-index 1- golf_array_slice
        result-arr swap golf_array_append
        new-index search-arr-len +
    repeat

    \ append the rest 
    base-arr last-index base-arr golf_array_len 1- 
    golf_array_slice
    result-arr swap golf_array_append
;


: golf_/_split_str_str ( typed-str1 typed-str2 -- typed-str3 )

    typeno_array coerce_to swap
    typeno_array coerce_to swap

    golf_/_split_arr_arr

    :noname POSTPONE typeno_str POSTPONE coerce_to POSTPONE ;
    anon_block
    golf_%
;


\ 
\ group functionality
\ 
: golf_/_group_array { typed-int typed-arr -- typed-arr }

    -1 
    golf_make_empty_array
    
    begin { last-index result-arr }

        last-index 
        typed-arr golf_array_len 1- <

    while 

        last-index typed-int val + 
        dup

        typed-arr last-index 1+ rot
        ( to-index typed-arr last-index+1 to-index -- )

        golf_array_slice 

        result-arr swap golf_array_append
    repeat

    result-arr
;


: golf_/_group_str ( typed-int typed-str -- typed-arr )

    typeno_array coerce_to 

    golf_/_group_array

    :noname POSTPONE typeno_str POSTPONE coerce_to POSTPONE ;
    anon_block
    golf_%
;

: golf_/_group ( typed-int typed-compound -- typed ) 

    dup golf_type CASE
        typeno_array OF golf_/_group_array ENDOF
        typeno_str OF  golf_/_group_str ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 
;



\ 
\ each functionality
\ 


: golf_/_each_array ( typed-compund typed-block -- varies ) 

    val
    golf_each 
;

: golf_/_each ( typed-compund typed-block -- varies ) 

    over golf_type CASE
        typeno_array OF golf_/_each_array ENDOF
        \ typeno_str OF  golf_/_each_str ENDOF
    ENDCASE 
;


\ 
\ strange unfold functionality
\ 

: golf_/_strange_unfold { typed-block-cond typed-block-exec -- varies }

    golf_make_empty_array

    begin { result-arr }
        dup 
        typed-block-cond val execute
        golf_boolean_to_flag
    while

        dup

        result-arr swap golf_array_append { result-arr }
        
        typed-block-exec val execute

        result-arr
    repeat

    drop \ if the check fails the saved var has to be deleted

    result-arr
;


\ 
\ / function routing
\ 
: golf_/ ( ty1 ty2 -- tyo )

    2dup 2op_same_type if

        dup golf_type CASE
            typeno_int OF golf_/_int_int ENDOF
            typeno_array OF golf_/_split_arr_arr ENDOF
            typeno_str OF  golf_/_split_str_str  ENDOF
            typeno_block OF golf_/_strange_unfold ENDOF
        ENDCASE 

        EXIT 
    then

    \ we have different operands
    2op_type_order 

    \ is the smaller one an integer? -> group split
    over golf_type typeno_int = if
        golf_/_group 
        EXIT
    then

    \ is the bigger one a block ? -> each 
    dup golf_type typeno_block = if
        golf_/_each
        EXIT
    then

    \  not reachable
    1 throw
;

\ --------------------------------
\ Golfscipt % Operator
\ -------------------------------

\ 
\ math functionality
\ 
: golf_%_int_int ( ty1 ty2 -- tyo )
    val swap val swap 
    mod anon_int 
;


\ 
\ split functionality
\ 

\ see the respective / functionality, 
\ but we have to filter empty arrays

: golf_%_split_arr_arr ( typed-arr1 typed-arr2 -- typed-arr3 )

  golf_/_split_arr_arr   
  :noname POSTPONE dup POSTPONE golf_! POSTPONE golf_boolean_to_flag 
          POSTPONE if POSTPONE drop POSTPONE then
          POSTPONE ;
  anon_block
  golf_%
;


: golf_%_split_str_str ( typed-str1 typed-str2 -- typed-str3 )

    typeno_array coerce_to swap
    typeno_array coerce_to swap

    golf_%_split_arr_arr

    :noname POSTPONE typeno_str POSTPONE coerce_to POSTPONE ;
    anon_block
    golf_%
;

\ 
\ index functionality
\ 

\ negative values revert index
: index_array_sort ( len u typedd-int -- u ) 
    val 0< if
        - 1-
    else
        nip    
    then 
;

: golf_%_index_array { typed-int typed-array -- } 

    typed-array golf_array_len { len }
    golf_slice_start
    len 0 u+do

        len i typed-int index_array_sort { index }

        index typed-int val abs mod 0= if 
            typed-array index golf_array_nth
        then
    loop
 
    anon_array
 ; 


: golf_%_index_str ( typed-int typed-str -- typed-str ) 

    typeno_array coerce_to
    golf_%_index_array 
    typeno_str coerce_to
;

: golf_%_index ( typed-int typed-compound ) 

    dup golf_type CASE
        typeno_array OF golf_%_index_array ENDOF
        typeno_str OF  golf_%_index_str ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 
;


\ 
\ map functionality
\ 
: golf_%_map_array_block { typed-arr typed-block -- typed-arr }

    golf_slice_start
    typed-arr typed-block val 
    golf_each
    anon_array 
;


: golf_%_map_str_block ( typed-str typed-block -- typed-str )

    swap typeno_array coerce_to
    swap golf_%_map_array_block

    typeno_str coerce_to
;

: golf_%_map ( typed-compound typed-block -- )

    over golf_type CASE
        typeno_array OF golf_%_map_array_block ENDOF
        typeno_str OF  golf_%_map_str_block  ENDOF
        typeno_block OF 1 throw ENDOF
    ENDCASE 
;


\ 
\ % function routing
\ 
: golf_%_impl ( ty1 ty2 -- tyo )

    2dup 2op_same_type if

        dup golf_type CASE
            typeno_int OF golf_%_int_int ENDOF
            typeno_array OF golf_%_split_arr_arr ENDOF
            typeno_str OF  golf_%_split_str_str  ENDOF
            typeno_block OF 1 throw ENDOF
        ENDCASE 

        EXIT 
    then

    \ we have different operands
    2op_type_order 

    \ is the smaller one an integer? -> index filter
    over golf_type typeno_int = if
        golf_%_index 
        EXIT
    then

    \ is the bigger one a block ? -> map 
    dup golf_type typeno_block = if
        golf_%_map
        EXIT
    then

    \  not reachable
    1 throw
;

' golf_%_impl IS golf_%


\ --------------------------------
\ - Golfscript * Operator
\ --------------------------------

: golf_*_intint { tyn1 tyn2 -- tyno }
    tyn1 val tyn2 val * anon_int ;

: golf_*_blockint { tyint tyblock  -- varies }
    tyint val 0 u+do
        tyblock golf_sim
    loop ;

: golf_*_arrint { tyint tyarr -- tyarr }
    golf_slice_start
    tyint val 0 u+do
        tyarr golf_sim
    loop
    anon_array ;

: golf_*_arrblock { tyarr tyblock -- varies }
    tyarr tyblock val golf_foldl ;

: golf_*_repeat ( tyn tystr typeid | tyn tyarr typeid -- tystr2 | tyarr2 )
    >r typeno_array coerce_to
    golf_*_arrint
    r> coerce_to ;

: golf_*_int ( varies -- ty1 )
    2op_type_order
    2dup 2op_max_type CASE
        typeno_int OF golf_*_intint ENDOF
        typeno_block OF golf_*_blockint ENDOF
        golf_*_repeat 1
    ENDCASE ;


: golf_*_arrarr { tyarr1 tyarr2 -- tyjoinedarr }
    golf_slice_start
    tyarr1 val nip 1-  0 u+do
        tyarr1 i golf_array_nth
        tyarr2 golf_sim
    loop
    tyarr1 dup val nip 1- golf_array_nth
    anon_array ;

: golf_*_join ( ty1 ty2 -- ty3 )
    2dup 2op_max_type >r
    typeno_array coerce_to swap
    typeno_array coerce_to swap
    golf_*_arrarr
    r> coerce_to ;

: golf_*_fold ( ty1 tyblock -- ty2 )
    swap typeno_array coerce_to swap golf_*_arrblock ;

: golf_* ( varies -- varies )
    2dup 2op_min_type typeno_int =
    IF golf_*_int ELSE
        2dup 2op_max_type typeno_str <=
        IF golf_*_join
        ELSE golf_*_fold
        ENDIF
    ENDIF ;
\ --------------------------------
\ - Golfscript ) Operator
\ --------------------------------
\ increment number
: golf_)_int ( tyn -- tyn+1 )
    val 1+ anon_int ;

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


\ --------------------------------
\ - Golfscript ( Operator
\ --------------------------------
\ increment number
: golf_(_int ( tyn -- tyn+1 )
    val 1- anon_int ;

: golf_(_array { tyarray -- tail head }
    tyarray 0 golf_array_nth
    golf_slice_start
    tyarray val nip 1 u+do
        tyarray i golf_array_nth
    loop
    anon_array swap ;

: golf_(
     dup golf_type CASE
         typeno_int OF golf_(_int ENDOF
         typeno_array OF golf_(_array ENDOF
     ENDCASE ;

\ --------------------------------
\ - Golfscript , Operator
\ --------------------------------

: golf_,_int { tyint -- tyarr }
    golf_slice_start
    tyint val 0 u+do
        i anon_int
    loop anon_array ;

: golf_,_arr ( tyarr -- tysz )
    val nip anon_int ;

: golf_,_block { tyarr tyblock -- tyfilteredarr }
    golf_slice_start
    tyarr val nip 0 u+do
        tyarr i golf_array_nth dup
        tyblock golf_sim golf_! val 0>
        IF drop ENDIF
    loop
    anon_array
;

: golf_, ( tyi -- tyo )
    dup golf_type CASE
        typeno_int OF golf_,_int ENDOF
        typeno_array OF golf_,_arr ENDOF
        typeno_block OF golf_,_block ENDOF
    ENDCASE ;

\ --------------------------------
\ - Golfscript ? Operator
\ --------------------------------

: golf_?_int { int1 int2 -- int1^int2 }
    int1 val int2 val
    1 swap 0 ?do over * loop nip anon_int ;

: golf_?_array { int array -- idxint }
    -1 array val 0 u+do
        dup @ int golf_equal_int
        IF nip i swap leave ELSE cell+ ENDIF
    loop drop anon_int ;

\ Vor dem if evtl anpassen
: golf_?_block { array block -- ... }
    array val nip  0 u+do
        array i golf_array_nth
        block golf_sim golf_! val 0= ( ! gives 0 on non-empty value )
        IF array i golf_array_nth LEAVE ENDIF
    loop ;

: golf_? ( varies varies -- ... )
    dup golf_type CASE
        typeno_int OF golf_?_int ENDOF
        typeno_array OF golf_?_array ENDOF
        typeno_block OF golf_?_block ENDOF
    ENDCASE ;



\ --------------------------------
\ - Golfscript zip Operator
\ --------------------------------
create arr_to_len :noname val nip anon_int ; ,
create tyint_max :noname val swap val max anon_int ; ,
: _max_inner_len ( arr -- n )
    arr_to_len anon_block golf_%_map
    tyint_max golf_foldr val ;

: golf_zip_t { tyarr tgt_type -- tyarrt }
    golf_slice_start
    tyarr _max_inner_len 0 u+do
        tyarr
        :noname i POSTPONE LITERAL POSTPONE anon_int POSTPONE golf_= POSTPONE ; \ map elements to index i
        anon_block golf_%_map  tgt_type coerce_to
    loop anon_array ;

: golf_zip { tyarr -- tyarrt }
    tyarr tyarr 0 golf_array_nth golf_type
    golf_zip_t ;

\ --------------------------------
\ - Golfscript abs Operator
\ --------------------------------
: golf_abs ( tyint -- +tyint )
    val abs anon_int ;

\ --------------------------------
\ - Golfscript base Operator
\ --------------------------------

: golf_base_intint { tyn tyradix -- tyarr }
    golf_slice_start
    tyn val
    begin
        dup tyradix val >= while
            tyradix val /mod swap anon_int swap
    repeat
    anon_int
    anon_array_reverse ;

: golf_base_arrint { tyarr tyradix -- tyint }
    tyradix val 0
    tyarr val nip 0 u+do
        tyarr i golf_array_nth val ( radix cur pos )
        + over *
    loop tyradix val / anon_int nip ;

: golf_base ( ty1 ty2 -- ty3 )
    2dup 2op_max_type CASE
        typeno_int OF golf_base_intint ENDOF
        typeno_array OF golf_base_arrint ENDOF
    ENDCASE ;

\ -----------------------------
\ - Golfscript stack operators
\ ----------------------------

: golf_.
   1 shift_down_slice_start
   dup ;
: golf_;  drop ;
: golf_backslash
    2 shift_down_slice_start
    swap ;
: golf_@  rot ;


\ --------------------------------
\ - Golfscript $ Operator
\ --------------------------------

: golf_$_int ( x0 ... xu tyu -- x0 ... xu x0 )
    val pick ;


: _map_to_sort_tuples { tyarr tyblock -- tuplearr }
    tyarr :noname POSTPONE golf_slice_start POSTPONE golf_. tyblock POSTPONE LITERAL
    POSTPONE golf_sim POSTPONE anon_array POSTPONE ;
    anon_block golf_%_map ;

: _compare_tuples { tyarr i j -- f }
    tyarr i golf_array_nth 1 golf_array_nth val
    tyarr j golf_array_nth 1 golf_array_nth val
    > ; ( XXX change to golf_> )
\ golf_> golf_boolean_to_flag ;

: _select_min { tyarr startidx -- minidx }
    startidx
    tyarr val nip startidx u+do
        dup tyarr swap i _compare_tuples
        IF drop i ENDIF
    loop ;

: _array_swap { tyarr x y -- tyarr }
    tyarr val drop dup ( addr addr )
    x cells + dup @ >r ( addr addr+x )
    swap y cells + dup @ ( addr+x addr+y yv )
    rot ! r> swap ! ;

: sort_tuples { tyarr -- tysorted }
    tyarr val nip 1- 0 u+do
        tyarr dup i _select_min
\        .s cr
        i _array_swap
    loop tyarr ;

create tuple_fst :noname 0 anon_int golf_= ; ,

: golf_$_block { tyarr tyblock -- sortedarr }
    tyarr tyblock _map_to_sort_tuples ( dup val_dump cr )
    sort_tuples
    tuple_fst anon_block golf_% ;

create std_sorter :noname ; anon_block ,
: golf_$ ( ty1 -- ty2 )
    dup golf_type CASE
        typeno_int OF golf_$_int ENDOF
        typeno_array OF
            std_sorter golf_$_block ENDOF
        typeno_block OF golf_$_block ENDOF
    ENDCASE ;

\ ----------------------------------------------
\ - Golfscript loop and conditional constructs
\ ----------------------------------------------

: golf_do { tyblock -- .. }
    BEGIN
        tyblock golf_sim
        golf_boolean_to_flag
    WHILE 
    REPEAT 
;

: golf_while { tyblock-condition tyblock-body -- .. }
    BEGIN
        tyblock-condition golf_sim  
        golf_boolean_to_flag
    WHILE 
        tyblock-body golf_sim
    REPEAT 
;

: golf_until { tyblock-condition tyblock-body -- .. }
    BEGIN
        tyblock-condition golf_sim  
        golf_boolean_to_flag invert
    WHILE 
        tyblock-body golf_sim
    REPEAT 
;



\ if a block is given we execute the typed, else we just leave it on the stack
: if_execute ( typed -- typed1) 
    dup golf_type 
    typeno_block = if 
        golf_sim
    then
;

: golf_if { ty1 ty2 ty3 --  }

    ty1 golf_boolean_to_flag if 
        ty2 if_execute
    else
        ty3 if_execute
    then
;

\ -----------------------------
\  Golfscript print operators
\ ----------------------------

: golf_print ( typed -- )
    typeno_str coerce_to
    val type
;

: golf_n ( -- typed-str)
    S\" \n" anon_str
;

: golf_puts ( typed -- )
    
    golf_print
    golf_n
    golf_print 
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
