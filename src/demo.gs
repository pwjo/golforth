
#
# type coercion and overloading
#

# + for coercion examples
12 3 +

'string' 'example' +

[ 65 ] [12] +

[ 65 ] 'rray' +

123:'esel'; 'esel' 12 +

# / and % for overloading


0 1 {100<} { .@+ } /

# Nested arrays and shifting slice starts
1 [2 [3\] 4 [..5]] 1 [[3\]]
    ->
[[3 1]]
[[3 2][4 4 4 5]]
1

# Soem high level operator examples
10,{3%},.,
    ->
6
[124578]

"hello world",{.+210>},
    ->
lloworl

['abc' '123' 'xyz']zip~
    ->
c3z
b2y
a1x

# mit extra rotate am schluss
1 [2 [3\] 4 [..5]] 1 [[3\]@]
    ->
[[[3 2] [4 4 4 5]] [3 1] 1]

# Grid Computing example from golfscript.com
'01 34 46 31 55 21 16 88 87 87 32 40 82 40 43 96 08 82 41 86 30 16 24 18 04 54 65 96 38 48 32 00 99 90 24 75 89 41 04 01 11 80 31 83 08 93 37 96 27 64 09 81 28 41 48 23 68 55 86 72 64 61 14 55 33 39 40 18 57 59 49 34 50 81 85 12 22 54 80 76 18 45 50 26 81 95 25 14 46 75 22 52 37 50 37 40 16 71 52 17'~]10/.zip+{{+}*}%$-1=

# Quine (from esolangs.org)
":@;[34]@+2*":@;[34]@+2*