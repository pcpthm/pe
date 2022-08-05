
-- [#1 Multiples of 3 or 5](https://projecteuler.net/problem=1)
namespace PE.P1

def sum n m := let x := (n - 1) / m; x * (x + 1) / 2 * m
def solve n := sum n 3 + sum n 5 - sum n (3 * 5)

def answer := solve 1000

end PE.P1

-- [#2 Even Fibonacci numbers](https://projecteuler.net/problem=2)
namespace PE.P2

def solve n := Id.run do
  let mut (a, b) := (0, 1)
  let mut sum := 0
  while a <= n do
    if a % 2 == 0 then
      sum := sum + a
    (a, b) := (a + b, a)
  return sum

def answer := solve 4000000

end PE.P2

-- [#3 Largest prime factor](https://projecteuler.net/problem=3)
namespace PE.P3

def solve n := Id.run do
  let mut max_p := 0
  let mut p := 2
  let mut n := n
  while p * p <= n do
    if n % p == 0 then
      max_p := max_p.max p
      while n % p == 0 do
        n := n / p
    p := p + 1
  return max_p.max n

def answer := solve 600851475143

end PE.P3

-- [#4 Largest palindrome product](https://projecteuler.net/problem=4)
namespace PE.P4

def isParin x := Id.run do
  let mut x := x
  let mut digits := #[]
  while x != 0 do
    digits := digits.push (x % 10)
    x := x / 10
  return digits == digits.reverse

def solve lo up := Id.run do
  let mut max := 0
  for x in [lo:up] do
    for y in [lo:up] do
      let prod := x * y
      if isParin prod then
        max := max.max prod
  return max

def answer := solve 100 1000

end PE.P4

def Std.Range.toArray (self : Std.Range) : Array Nat := Id.run do
  let mut res := #[]
  for x in self do
    res := res.push x
  return res

-- [#5 Smallest multiple](https://projecteuler.net/problem=5)
namespace PE.P5

def lcm (x y : Nat) := x * y / x.gcd y

def solve n := [1:n+1].toArray |>.foldl lcm 1

def answer := solve 20

end PE.P5

-- [#6 Sum square difference](https://projecteuler.net/problem=6)
namespace PE.P6

def solve n := [1:n+1].toArray.foldl (· + ·) 0 ^ 2 - [1:n+1].toArray.foldl (· + · ^ 2) 0

def answer := solve 100

end PE.P6

-- [#7 10001st prime](https://projecteuler.net/problem=7)
namespace PE.P7

def sieve (n : Nat) : Array Nat := Id.run do
  let mut crossed := mkArray (n+1) false
  let mut primes := #[]
  for p in [2:n+1] do
    if !crossed[p]! then
      primes := primes.push p
      let mut m := p * 2
      while m <= n do
        crossed := crossed.set! m true
        m := m + p
  return primes

partial def loop k n :=
  let primes := sieve n
  if h : k < primes.size then
    primes[k]
  else
    loop k (n * 2)

def solve n := loop (n - 1) 1

def answer := solve 10001

end PE.P7

def Char.isDigit? (self : Char) : Option Nat :=
  if self.isDigit then
    some (self.toNat - '0'.toNat)
  else
    none

-- [#8 Largest product in a series](https://projecteuler.net/problem=8)
namespace PE.P8

def theNumbers : IO (Array Nat) := do
  let string ← IO.FS.readFile ("data" / "p8.txt")
  let mut res := #[]
  for c in string.toList do
    if let some d := c.isDigit? then
      res := res.push d
  return res

def solve (numbers : Array Nat) (n : Nat) : Nat := Id.run do
  let mut max := 0
  for i in [0:numbers.size+1-n] do
    let prod := numbers[i:i+n].toArray.foldl (· * ·) 1
    max := max.max prod
  return max

def answer := (solve · 13) <$> theNumbers

end PE.P8

-- <https://github.com/leanprover/lean4/issues/1420>
deriving instance Inhabited for MProd

-- [#9 Special Pythagorean triplet](https://projecteuler.net/problem=9)
namespace PE.P9

def solve (sum : Nat) := Id.run do
  for a in [1:sum] do
    for b in [a+1:sum-a] do
      let c := sum - (a + b)
      if b < c ∧ a^2 + b^2 = c^2 then
        return a * b * c
  return 0

def answer := solve 1000

end PE.P9

-- [#10 Summation of primes](https://projecteuler.net/problem=10)
namespace PE.P10

def solve n := P7.sieve n |>.foldl (· + ·) 0

def answer := solve 2000000

end PE.P10

