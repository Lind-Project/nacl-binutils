#objdump: -s -j .drectve
#name: aligned common D

# Test the aligned form of the .comm pseudo-op.

.*: .*

Contents of section .drectve:
 0000 202d616c 69676e63 6f6d6d3a 5f682c38   -aligncomm:_h,8
 0010 202d616c 69676e63 6f6d6d3a 5f692c34   -aligncomm:_i,4
 0020 202d616c 69676e63 6f6d6d3a 5f6a2c32   -aligncomm:_j,2
 0030 202d616c 69676e63 6f6d6d3a 5f6b2c31   -aligncomm:_k,1
