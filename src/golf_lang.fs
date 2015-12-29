1 constant typeno_int
2 constant typeno_str
3 constant typeno_block
4 constant typeno_array

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
        typeno_int OF . ENDOF
        typeno_str OF type ENDOF
        typeno_block OF . ENDOF
        typeno_array OF
            0 u+do dup i cells + @ recurse loop
            drop
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

\ ------------------------
\ - Anonyme konstruktoren
\ ------------------------
: anon_int { u -- typext }
    :noname  u POSTPONE LITERAL POSTPONE typeno_int  POSTPONE ; ;

: anon_str { addr u -- typext }
    :noname  addr POSTPONE LITERAL u POSTPONE LITERAL POSTPONE typeno_str POSTPONE ; ;

: anon_block { xt -- typext }
    :noname  xt POSTPONE LITERAL POSTPONE typeno_block POSTPONE ; ;


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
    dup golf_type CASE
        typeno_int OF golf_+_int ENDOF
        typeno_array OF golf_+_array ENDOF
        typeno_str OF golf_+_str ENDOF
        typeno_block OF golf_+_block ENDOF
    ENDCASE ;

\ --------------------------------
\ - Golfscipt - Operator
\ -------------------------------
: golf_-_int { ty1 ty2 -- tyo }
    ty1 val ty2 val - anon_int ;

: golf_- ( ty1 ty2 -- tyo )
    dup golf_type CASE
        typeno_int OF golf_-_int ENDOF
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
\ - Golfscript simple operators
\ ----------------------------
: golf_.  dup ;
: golf_;  drop ;
: golf_backslash  swap ;
: golf_@  rot ;

\ ------------------------
\ - Golfscript do
\ ------------------------
 : golf_do { tyblock -- .. }
    BEGIN
        tyblock golf_sim
        val
    WHILE 
    REPEAT 
;

\ ------------------------
\ - Triviale operatoren
\ --------------------------
: golf_@ rot ;
: golf_; drop ;
: golf_. dup ;
: golf_\ swap ;


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
