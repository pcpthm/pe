import Std

-- [#1 Multiples of 3 or 5](https://projecteuler.net/problem=1)
namespace PE.P1

def sum n m := let x := (n - 1) / m; x * (x + 1) / 2 * m
def solve n := sum n 3 + sum n 5 - sum n (3 * 5)

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

def solve k := Id.run do
  let lo := 10^k
  let up := 10^(k+1)
  let mut max := 0
  for x in [lo:up] do
    for y in [lo:up] do
      let prod := x * y
      if isParin prod then
        max := max.max prod
  return max

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

end PE.P5

-- [#6 Sum square difference](https://projecteuler.net/problem=6)
namespace PE.P6

def solve n := [1:n+1].toArray.foldl (· + ·) 0 ^ 2 - [1:n+1].toArray.foldl (· + · ^ 2) 0

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

end PE.P7

def Char.isDigit? (self : Char) : Option Nat :=
  if self.isDigit then
    some (self.toNat - '0'.toNat)
  else
    none

-- [#8 Largest product in a series](https://projecteuler.net/problem=8)
namespace PE.P8

def parse (lines : Array String) : Array Nat := Id.run do
  let mut res := #[]
  for line in lines do
    for c in line.toList do
      if let some d := c.isDigit? then
        res := res.push d
  return res

def solve (numbers : Array Nat) (n : Nat) : Nat := Id.run do
  let mut max := 0
  for i in [0:numbers.size+1-n] do
    let prod := numbers[i:i+n].toArray.foldl (· * ·) 1
    max := max.max prod
  return max

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

end PE.P9

-- [#10 Summation of primes](https://projecteuler.net/problem=10)
namespace PE.P10

def solve n := P7.sieve n |>.foldl (· + ·) 0

end PE.P10

-- [#11 Largest product in a grid](https://projecteuler.net/problem=11)
namespace PE.P11

def parse (lines : Array String) : Array (Array Nat) :=
  lines.map (·.split (· == ' ') |>.map (·.toNat!) |>.toArray)

def prod : Array Nat → Nat := Array.foldl (· * ·) 1

def solve (matrix : Array (Array Nat)) n := Id.run do
  let h := matrix.size
  let w := matrix[0]!.size
  let mut max := 0
  for i in [0:h] do
    for j in [0:w] do
      if i + n <= h then
        max := max.max $ prod $ [0:n].toArray |>.map (matrix[i + ·]![j]!)
      if j + n <= w then
        max := max.max $ prod $ [0:n].toArray |>.map (matrix[i]![j + ·]!)
      if i + n <= h && j + n <= w then
        max := max.max $ prod $ [0:n].toArray |>.map (fun k => matrix[i + k]![j + k]!)
      if i + n <= h && n - 1 <= j then
        max := max.max $ prod $ [0:n].toArray |>.map (fun k => matrix[i + k]![j - k]!)
  return max

end PE.P11

-- [#12 Highly divisible triangular number](https://projecteuler.net/problem=12)
namespace PE.P12

def factors (n : Nat) : Array (Nat × Nat) := Id.run do
  let mut factors := #[]
  let mut n := n
  let mut p := 2
  while p * p <= n do
    let mut k := 0
    while n % p == 0 do
      k := k + 1
      n := n / p
    if k != 0 then
      factors := factors.push (p, k)
    p := p + 1
  if n != 1 then
    factors := factors.push (n, 1)
  return factors

def numDivisors n := factors n |>.foldl (fun (_, k) => (k + 1) * ·) 1

def solve n := Id.run do
  let mut x := 0
  let mut y := 0
  repeat
    x := x + 1
    y := y + x
  until numDivisors y > n
  return y

end PE.P12

-- [#13 Large sum](https://projecteuler.net/problem=13)
namespace PE.P13

def parse (lines : Array String) : Array Nat :=
  lines.map (·.toNat!)

def getDigits (n : Nat) : Array Nat := Id.run do
  let mut n := n
  let mut digits := #[]
  while n != 0 do
    digits := digits.push (n % 10)
    n := n / 10
  return digits

def firstDigits k n := n / 10^((getDigits n).size - k)

def solve (numbers : Array Nat) k := numbers |>.foldl (· + ·) 0 |> firstDigits k

end PE.P13

-- [#14 Longest Collatz sequence](https://projecteuler.net/problem=14)
namespace PE.P14
open Std

def next (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1

abbrev M := StateM (HashMap Nat Nat)

partial def solveRec (n : Nat) : M Nat := do
  if let some res := (← get).find? n then
    return res
  else if n <= 1 then
    return 1
  else
    let res := (← solveRec (next n)) + 1
    modify (·.insert n res)
    return res

def solveAux (n : Nat) : M (Nat × Nat) := do
  let mut max := (0, 0)
  for x in [1:n] do
    let len ← solveRec x
    if max.1 < len then
      max := (len, x)
  return max

def M.run (self : M α) : α := self.run' HashMap.empty

def solve n := solveAux n |>.run |>.2

end PE.P14

-- [#15 Lattice paths](https://projecteuler.net/problem=15)
namespace PE.P15
open Std

abbrev M := StateM (HashMap (Nat × Nat) Nat)
def M.run (self : M α) : α := self.run' HashMap.empty

partial def solveRec (i j : Nat) : M Nat := do
  if let some res := (← get).find? (i, j) then
    return res
  else if i == 0 && j == 0 then
    return 1
  else
    let mut res := 0
    if i != 0 then
      res := res + (← solveRec (i - 1) j)
    if j != 0 then
      res := res + (← solveRec i (j - 1))
    modify (·.insert (i, j) res)
    return res

def solve n := solveRec n n |>.run

end PE.P15

-- [#16 Power digit sum](https://projecteuler.net/problem=16)
namespace PE.P16

def solve n := P13.getDigits (2^n) |>.foldl (· + ·) 0

end PE.P16

-- [#17 Number letter counts](https://projecteuler.net/problem=17)
namespace PE.P17

def names₁ := #[
  "","one","two","three","four","five","six","seven","eight","nine",
  "ten","eleven","twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"]

def names₂ := #["","","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"]

def toEnglish2 (n : Nat) :=
  if n < 20 then
    names₁[n]!
  else if n % 10 == 0 then
    names₂[n / 10]!
  else
    s!"{names₂[n / 10]!} {names₁[n % 10]!}"

def toEnglish3 (n : Nat) : String :=
  if n < 100 then
    toEnglish2 n
  else if n % 100 == 0 then
    s!"{names₁[n/100]!} hundred"
  else
    s!"{names₁[n/100]!} hundred and {toEnglish2 (n % 100)}"

def toEnglish n := if n < 1000 then toEnglish3 n else "one thousand"

def englishLen (n : Nat) : Nat :=
  (toEnglish n).toList.filter (· != ' ') |>.length

def solve n := [1:n+1].toArray.map englishLen |>.foldl (· + ·) 0

end PE.P17

-- [#18 Maximum path sum I](https://projecteuler.net/problem=18)
namespace PE.P18
open Std

abbrev M := ReaderT (Array (Array Nat)) (StateM (HashMap (Nat × Nat) Nat))

partial def solveRec (i j : Nat) : M Nat := do
  let triangle ← read
  if let some res := (← get).find? (i, j) then
    return res
  else if i >= triangle.size then
    return 0
  else
    let res := triangle[i]![j]! + (← solveRec (i+1) j).max (← solveRec (i+1) (j+1))
    modify (·.insert (i, j) res)
    return res

def solve triangle (_ : Nat) :=
  ((solveRec 0 0).run triangle).run' HashMap.empty

def parse (lines : Array String) : Array (Array Nat) :=
  lines.map (·.split (· == ' ') |>.map (·.toNat!) |>.toArray)

end PE.P18

-- [#19 Counting Sundays](https://projecteuler.net/problem=19)
namespace PE.P19

def isLeapYear (y : Nat) := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def monthDays y m :=
  30 + (if m matches 2 | 4 | 6 | 9 | 11 then 0 else 1) -
  (if m == 2 then (if isLeapYear y then 1 else 2) else 0)

def solve lastYear := Id.run do
  let mut res := 0
  let mut dow := 1
  for year in [1900:lastYear+1] do
    for month in [1:12+1] do
      if year >= 1901 && dow == 0 then
        res := res + 1
      dow := (dow + monthDays year month) % 7
  return res

end PE.P19

-- [#20 Factorial digit sum](https://projecteuler.net/problem=20)
namespace PE.P20

def solve n := [1:n+1].toArray.foldl (· * ·) 1 |> P13.getDigits |>.foldl (· + ·) 0

end PE.P20
