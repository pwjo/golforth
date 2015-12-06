s" regex.fth" included 

s" ((u(v+)w)*(x(y+)z)*)+" regex$ constant rgx1 

: .results  ( caddr u f -- ) 
    if 
       cr ." Unused: " type 
       s" \nMatch: \M\nSub-expressions: \1, \2, \3, \4, \5\n" 
       stringer$ type 
    else 
       cr ." No match" 2drop 
    then 
; 

s" uvvwxyyyzabc" rgx1 match .results 
