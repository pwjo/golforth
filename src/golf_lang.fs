1 constant typeno_int
2 constant typeno_str
3 constant typeno_block
4 constant typeno_array

( Nur ein Level atm )
create slice_start 0 ,

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
: golf_slice_start ( -- )
    depth slice_start ! ;

: make_array_xt { addr n -- }
    :noname addr POSTPONE LITERAL n POSTPONE LITERAL POSTPONE typeno_array POSTPONE ; ;

: anon_array
    here depth slice_start @ - 1- dup >r
    dup cells dup  allot
    rot + swap
    0 u+do
        cell - tuck !
    loop r>
    make_array_xt ;

\ ------------------------
\ - Anonyme konstruktoren
\ ------------------------
: anon_int { u -- typext }
    :noname  u POSTPONE LITERAL POSTPONE typeno_int  POSTPONE ; ;

: anon_str { addr u -- typext }
    :noname  addr POSTPONE LITERAL u POSTPONE LITERAL POSTPONE typeno_str POSTPONE ; ;

: anon_block { addr u -- typext }
    :noname  addr POSTPONE LITERAL u POSTPONE LITERAL POSTPONE typeno_block POSTPONE ; ;

\ -----------------------------
\ - Projektionen
\ -----------------------------
: golf_type ( ty -- t )
    execute dup  CASE
        typeno_int OF nip ENDOF
        typeno_str OF nip nip ENDOF
        typeno_block OF nip nip ENDOF
        typeno_array OF nip nip ENDOF
    ENDCASE ;

: val ( xt -- x )
    execute drop ;

\ -----------------------------
\ - Golfscript ~ Operator
\ ----------------------------
: golf_sim_str ( tstr -- )
    drop ( eval stuff ) ;

: golf_sim_int ( tu -- typedxt )
    val invert anon_int ;

: golf_sim_array ( tarr -- )
    val 0 u+do
        dup i cells + @ tuck drop
    loop drop ;

: golf_sim ( typed -- ... )
    dup golf_type CASE
        typeno_int OF golf_sim_int ENDOF
        typeno_str OF  golf_sim_str ENDOF
        typeno_block OF golf_sim_str ENDOF
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

: golf_+ ( ty1 ty2 -- tyo )
    dup golf_type CASE
        typeno_int OF golf_+_int ENDOF
        typeno_array OF golf_+_array ENDOF
    ENDCASE ;


\ ------------------------
\ - Golfscript do
\ ------------------------
: golf_do { tyblock -- .. }
    BEGIN
        tyblock golf_sim
    UNTIL ;

\ ------------------------
\ - Triviale operatoren
\ --------------------------
: golf_@ rot ;
: golf_; drop ;


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
