#
# basic + functionality
#

# integer
12 1 +
13

# array
[2] [65 66] +
[26566]

# string
'esel' 'hund' +
eselhund

# block
1 {2} {+} + ~
3

#
# coercion
#

# integer / array
12 [1] +
[121]

[1] 3+
[13]

# integer / string
12 '1' +
121

'a' 3+
a3


# integer / block
1 2 {+} + . + ~
5

1 2 {+} 2 + . + ~
2
5


# TODO array / string
# [65] 'rray' +
# Array

# TODO array / block


# string / block
12:esel 'esel+' {1}+ ~
1
24
