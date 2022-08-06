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

-- [#21 Amicable numbers](https://projecteuler.net/problem=21)
namespace PE.P21

def sod₁ p k := (p^(k+1) - 1) / (p - 1)

def sod n := P12.factors n |>.map (fun (p, k) => sod₁ p k) |>.foldl (· * ·) 1

def solve n := Id.run do
  let mut sum := 0
  for a in [1:n+1] do
    let b := sod a - a
    if a != b && sod b - b == a then
      sum := sum + a
  return  sum

end PE.P21

-- [#22 Names scores](https://projecteuler.net/problem=22)
namespace PE.P22

def parse (lines : Array String) : Array String :=
  lines[0]!.split (· == ',') |>.map (·.drop 1 |>.dropRight 1) |>.toArray

def value (s : String) := s.toList.map (·.toNat - 'A'.toNat + 1) |>.foldr (· + ·) 0

def solve (names : Array String) (_ : Nat) :=
  names.qsort (· < ·) |>.mapIdx (fun i s => value s * (i.val + 1)) |>.foldl (· + ·) 0

end PE.P22

-- [#23 Non-abundant sums](https://projecteuler.net/problem=23)
namespace PE.P23

def solve n := Id.run do
  let as := [1:n+1].toArray.filter (fun n => P21.sod n > n * 2)
  let mut isA := mkArray (n+1) false
  for a in as do
    isA := isA.set! a true
  let mut res := 0
  for x in [1:n+1] do
    let isSum := as.any (fun a => isA.getD (x - a) false)
    if !isSum then
      res := res + x
  return res

end PE.P23

-- [#24 Lexicographic permutations](https://projecteuler.net/problem=24)
namespace PE.P24

def fnsToPerm (fns : Array Nat) : Array Nat := Id.run do
  let n := fns.size
  let mut perm := #[]
  let mut used := mkArray n false
  for i in [0:n] do
    let mut k := fns[n - 1 - i]!
    for x in [0:n] do
      if !used[x]! then
        if k == 0 then
          used := used.set! x true
          perm := perm.push x
          break
        k := k - 1    
  return perm

def rankToFns (n : Nat) (rank : Nat) : Array Nat := Id.run do
  let mut fns := #[]
  let mut k := rank
  for i in [0:n] do
    fns := fns.push (k % (i + 1))
    k := k / (i + 1)
  return fns

def rankToPerm n rank := fnsToPerm (rankToFns n rank)

def fromDigits (digits : Array Nat) : Nat :=
  digits.foldl (· * 10 + ·) 0

def solve (n : Nat) :=
  let perm := rankToPerm 10 (n - 1)
  fromDigits perm

end PE.P24

-- [#25 1000-digit Fibonacci number](https://projecteuler.net/problem=25)
namespace PE.P25

def solve (n : Nat) := Id.run do
  let n := 10^(n-1)
  let mut (a, b) := (0, 1)
  let mut i := 0
  while a < n do
    (a, b) := (a + b, a)
    i := i + 1
  return i

end PE.P25

-- [#26 Reciprocal cycles](https://projecteuler.net/problem=26)
namespace PE.P26

def getCycleLength (n : Nat) := Id.run do
  let mut used := mkArray n false
  let mut len := 0
  let mut r := 1
  while !used[r]! do
    used := used.set! r true
    r := r * 10 % n
    len := len + 1
  return len

def solve (n : Nat) := Id.run do
  let mut max := (0, 0)
  for x in [2:n] do
    if x % 2 == 0 || x % 5 == 0 then
      continue
    let len := getCycleLength x
    if max.fst < len then
      max := (len, x)
  return max.snd

end PE.P26

-- [#27 Quadratic primes](https://projecteuler.net/problem=27)
namespace PE.P27

def isPrime (n : Nat) : Bool := Id.run do
  let mut p := 2
  while p * p <= n do
    if n % p == 0 then
      return false
    p := p + 1
  return n > 1

partial def getNumConsecutivePrimes (a b : Int) : Nat :=
  let rec loop (n : Int) :=
    let y: Int := n^2 + a * n + b
    if 0 <= y && isPrime y.toNat then
      1 + loop (n + 1)
    else
      0
  loop 0

def solve (limit : Nat) : Int := Id.run do
  let primes := [2:limit+1].toArray.filter isPrime
  let mut max := (0, 0)
  let mut a: Int := -Int.ofNat limit + 1
  while a < limit do
    for b in primes do
      let num := getNumConsecutivePrimes a b
      if max.fst < num then
        max := (num, a * b)
    a := a + 1
  return max.snd

end PE.P27

-- [#28 Number spiral diagonals](https://projecteuler.net/problem=28)
namespace PE.P28

def solve (n : Nat) := Id.run do
  let mut sum := 1
  let mut start := 2
  for k in [1:n/2+1] do
    let len := k * 2 + 1
    let num := len^2 - (len-2)^2
    for i in #[len - 2, len * 2 - 3, len * 3 - 4, num - 1] do
      sum := sum + (start + i)
    start := start + num
  return sum

end PE.P28

-- [#29 Distinct powers](https://projecteuler.net/problem=29)
namespace PE.P29
open Std (HashSet)

def solve (n : Nat) := Id.run do
  let mut set := HashSet.empty
  for a in [2:n+1] do
    let as := P12.factors a
    for b in [2:n+1] do
      let pow := as.map (fun (p, k) => (p, k * b))
      set := set.insert pow
  return set.size

end PE.P29

-- [#30 Digit fifth powers](https://projecteuler.net/problem=30)
namespace PE.P30

def solve (n : Nat) := Id.run do
  let mut len := 2
  let mut sum := 0
  while 10^(len-1) <= 9^n * len do
    for x in [10^(len-1):10^len] do
      if (P13.getDigits x |>.map (· ^ n) |>.foldl (· + ·) 0) == x then
        sum := sum + x
    len := len + 1
  return sum

end PE.P30

-- [#31 Coin sums](https://projecteuler.net/problem=31)
namespace PE.P31
open Std (HashMap)

abbrev M := StateM $ HashMap (Nat × Nat) Nat

def coins := #[1,2,5,10,20,50,100,200]

partial def solveRec (i : Nat) (rem : Nat) : M Nat := do
  if let some res := (← get).find? (i, rem) then
    return res
  else if h : i < coins.size then
    let mut res ← solveRec (i+1) rem
    if coins[i] <= rem then
      res := res + (← solveRec i (rem - coins[i]))
    modify (·.insert (i, rem) res)
    return res
  else
    return if rem == 0 then 1 else 0

def solve (n : Nat) := solveRec 0 n |>.run' HashMap.empty

end PE.P31

-- [#32 Pandigital products](https://projecteuler.net/problem=32)
namespace PE.P32
open Std (HashSet)

def solve (n : Nat) := Id.run do
  let mut set := HashSet.empty
  for len1 in [1:5+1] do
    for len2 in [len1:5+1] do
      let lenProd := len1 + len2 - 1
      let lenTotal := len1 + len2 + lenProd
      if lenTotal != n then
        continue
      for y in [10^(len2-1):10^len2] do
        let mut used := mkArray 10 false
        let mut bad := false
        for d in P13.getDigits y do
          bad := bad || used.get! d || d == 0
          used := used.set! d true
        if bad then
          continue
        for x in [10^(len1-1):10^len1] do
          let mut bad2 := false
          let mut used2 := used
          for d in P13.getDigits x do
            bad2 := bad2 || used2.get! d || d == 0
            used2 := used2.set! d true
          if bad2 then
            continue
          let prod := x * y
          for d in P13.getDigits prod do
              bad2 := bad2 || used2.get! d || d == 0
              used2 := used2.set! d true
          if bad2 then
            continue
          set := set.insert prod
  return set.toList.foldr (· + ·) 0

end PE.P32

-- [#33 Digit cancelling fractions](https://projecteuler.net/problem=33)
namespace PE.P33
open Std (HashSet)

def mkFrac x y := let g := Nat.gcd x y; (x / g, y / g)

def solve (n : Nat) := Id.run do
  let mut prod := (1, 1)
  for x in [10^(n-1):10^n] do
    for y in [10^(n-1):10^n] do
      if x >= y then
        continue
      let frac := mkFrac x y
      if x % 10 == y / 10 && frac == mkFrac (x / 10) (y % 10) then
        prod := mkFrac (prod.fst * x) (prod.snd * y)
  return prod.snd

end PE.P33

-- [#34 Digit factorials](https://projecteuler.net/problem=34)
namespace PE.P34

abbrev M := ReaderT (Array (Nat × Nat)) Id

partial def solveRec (cur : Array Nat) (sum : Nat) (prev : Nat) : M Nat := do
  let mut res := 0
  if cur.size > 1 && (P13.getDigits sum).qsort (· < ·) == cur then
    res := res + sum
  for (d, fact) in ← read do
    if prev <= d && cur.size <= 5 then
      res := res + (← solveRec (cur.push d) (sum + fact) d)
  return res

def factorials := Id.run do
  let mut fact := #[(0, 1)]
  for i in [1:10] do
    fact := fact.push (i, fact[fact.size-1]!.snd * i)
  return fact

def solve (n : Nat) := (solveRec #[] 0 0).run factorials |>.max n -- max is just for using the argument.

end PE.P34

-- [#35 Circular primes](https://projecteuler.net/problem=35)
namespace PE.P35
open Std (HashSet)

partial def digitLen n := if n < 10 then 1 else digitLen (n / 10) + 1

def solve (n : Nat) := Id.run do
  let primes := P7.sieve n
  let primeSet := primes.foldl (·.insert ·) HashSet.empty
  let mut len := 1
  let mut tens := 1
  let mut num := 0
  for p in primes do
    while tens * 10 <= p do
      len := len + 1
      tens := tens * 10
    let mut ok := true
    let mut x := p
    for _ in [0:len-1] do
      x := x / 10 + tens * (x % 10)
      unless primeSet.contains x do
        ok := false
        break
    if ok then
      num := num + 1
  return num

end PE.P35

-- [#36 Double-base palindromes](https://projecteuler.net/problem=36)
namespace PE.P36

def reverseDigits (base : Nat) (n : Nat) := Id.run do
  let mut res := 0
  let mut n := n
  while n > 0 do
    res := res * base + n % base
    n := n / base
  return res

def solve (n : Nat) := Id.run do
  let mut sum := 0
  let mut halfLen := 1
  while 10^(halfLen * 2 - 2) < n do
    for half in [10^(halfLen-1):10^halfLen] do
      let pal1 := half * 10^(halfLen-1) + reverseDigits 10 (half / 10)
      let pal2 := half * 10^halfLen + reverseDigits 10 half
      for pal in #[pal1, pal2] do
        if pal < n && reverseDigits 2 pal == pal then
          sum := sum + pal
    halfLen := halfLen + 1
  return sum

end PE.P36

-- [#37 Truncatable primes](https://projecteuler.net/problem=37)
namespace PE.P37

def isRightTruncPrime n := Id.run do
  let mut tens := 10
  while tens <= n do
    if !P27.isPrime (n % tens) then
      return false
    tens := tens * 10
  return true

partial def solveRec (cur : Nat) : Nat := Id.run do
  if cur != 0 && !P27.isPrime cur then
    return 0
  let mut res := 0
  if cur >= 10 && isRightTruncPrime cur then
    res := res + cur
  for d in [1:10] do
    res := res + solveRec (cur * 10 + d)
  return res

def solve (n : Nat) := solveRec 0 |>.max n -- max is only for using the input

end PE.P37

-- [#38 Pandigital multiples](https://projecteuler.net/problem=38)
namespace PE.P38

def solve (n : Nat) := Id.run do
  let mut max := 0
  for len in [1:9/2+1] do
    for a in [10^(len-1):10^len] do
      let mut mul := a
      let mut digits := #[]
      while digits.size < 9 do
        digits := digits.append (P13.getDigits mul).reverse
        mul := mul + a
      if digits.size == 9 && digits.qsort (· < ·) == #[1,2,3,4,5,6,7,8,9] then
        let num := digits.foldl (· * 10 + ·) 0
        max := max.max num
  return max.max n -- max is only for using the input

end PE.P38

-- [#39 Integer right triangles](https://projecteuler.net/problem=39)
namespace PE.P39
open Std (HashMap)

-- Ref: [Tree of primitive Pythagorean triples - Wikipedia](https://en.wikipedia.org/wiki/Tree_of_primitive_Pythagorean_triples)
partial def ptTree (bound : Nat) (m n : Nat) : StateM (Array (Nat × Nat × Nat)) Unit := do
  if m^2 + n^2 <= bound then
    modify (·.push (m^2 - n^2, 2 * m * n, m^2 + n^2))
    ptTree bound (m * 2 - n) m
    ptTree bound (m * 2 + n) m
    ptTree bound (m + n * 2) n

def enumPPT bound := ptTree bound 2 1 |>.run #[] |>.snd

def enumPT bound := Id.run do
  let mut res := #[]
  for (a, b, c) in enumPPT bound do
    for f in [1:bound/5+1] do
      res := res.push (a * f, b * f, c * f)
  return res

def solve (n : Nat) := Id.run do
  let mut count := HashMap.empty
  for (a, b, c) in enumPT n do
    let p := a + b + c
    if p <= n then
      count := count.insert p ((count.find? p).getD 0 + 1)
  let mut max := (0, 0)
  for (p, k) in count.toArray do
    if max.fst < k then
      max := (k, p)
  return max.snd

end PE.P39

-- [#40 Champernowne's constant](https://projecteuler.net/problem=40)
namespace PE.P40

def getDigit (k : Nat) := Id.run do
  let mut k := k
  let mut len := 1
  repeat
    let total := len * (10^len - 10^(len-1))
    if k < total then
      break
    k := k - total
    len := len + 1
  let num := 10^(len-1) + k / len
  return (P13.getDigits num)[len - 1 - k % len]!

def solve (n : Nat) := Id.run do
  let mut prod := 1
  for k in [0:n+1] do
    prod := prod * getDigit (10^k - 1)
  return prod

end PE.P40

-- [#41 Pandigital prime](https://projecteuler.net/problem=41)
namespace PE.P41

def nextPermutationAux (perm : Array Nat) : Nat × Nat := Id.run do
  let mut i := perm.size
  while i > 1 && perm[i - 2]! >= perm[i - 1]! do
    i := i - 1
  if i <= 1 then
    return (perm.size, perm.size)
  let mut j := perm.size - 1
  while perm[i - 2]! >= perm[j]! do
    j := j - 1
  return (i - 2, j)

def applySwapRev (perm : Array Nat) (i j : Nat) := Id.run do
  let mut perm := perm.swap! i j
  let mut i := i + 1
  let mut k := perm.size - 1
  while i < k do
    perm := perm.swap! i k
    i := i + 1
    k := k - 1
  return perm

structure Permutations where
  cur : Array Nat

partial instance : ForIn m Permutations (Array Nat) where
  forIn start b f :=
    let rec loop cur b := do
      match ← f cur b with
      | .done b => return b
      | .yield b =>
        let (i, j) := nextPermutationAux cur
        if i < cur.size then
          let next := applySwapRev cur i j
          loop next b
        else
          return b
    loop start.cur b

def solve (n : Nat) := Id.run do
  let mut max := 0
  for len in [2:n+1] do
    for perm in Permutations.mk [1:len+1].toArray do
      if perm[0]! % 2 == 0 then
        continue
      let num := perm.foldr (· + · * 10) 0
      if P27.isPrime num then
        max := max.max num
  return max

end PE.P41

-- [#42 Coded triangle numbers](https://projecteuler.net/problem=42)
namespace PE.P42
open Std (HashSet)

def parse := P22.parse

def solve (words: Array String) (_ : Nat) := Id.run do
  let values := words.map P22.value
  let maxValue := values.foldl Nat.max 0
  let mut set := HashSet.empty
  let mut cur := 1
  let mut i := 2
  while cur <= maxValue do
    set := set.insert cur
    cur := cur + i
    i := i + 1
  return values.filter (set.contains ·) |>.size

end PE.P42

-- [#43 Sub-string divisibility](https://projecteuler.net/problem=43)
namespace PE.P43

partial def solveRec (n : Nat) (i : Nat) (cur : Nat) (used : Nat) : Nat := Id.run do
  if i >= 3 then
    let m := #[17,13,11,7,5,3,2,1][i-3]!
    if cur / 10^(i-3) % m != 0 then
      return 0
  if i == n then
    return cur
  let mut sum := 0
  for d in [0:10] do
    if used &&& (1 <<< d) != 0 then
      continue
    if i + 1 == n && d == 0 then
      continue
    sum := sum + solveRec n (i + 1) (cur + d * 10^i) (used ||| (1 <<< d))
  return sum

def solve (n : Nat) : Nat := solveRec n 0 0 0

end PE.P43

-- [#44 Pentagon numbers](https://projecteuler.net/problem=44)
namespace PE.P44
open Std (HashSet)

-- n must be a some large number
def solve (n : Nat) := Id.run do
  let ps := [1:n].toArray.map (fun n => n * (3 * n - 1) / 2)
  let set := ps.foldl (·.insert ·) HashSet.empty
  for d in ps do
    let mut preva := 0
    for a in ps do
      if a - preva > d then
        break
      preva := a
      let b := a + d
      if set.contains b then
        if set.contains (a + b) then
          return d
  return 0

end PE.P44

-- [#45 Triangular, pentagonal, and hexagonal](https://projecteuler.net/problem=45)
namespace PE.P45
open Std (HashSet)

-- n must be a some large number
def solve n := Id.run do
  let ts := [1:n].toArray.map (fun n => n * (n + 1) / 2) |>.foldl (·.insert ·) HashSet.empty
  let ps := [1:n].toArray.map (fun n => n * (3 * n - 1) / 2) |>.foldl (·.insert ·) HashSet.empty
  for a in [2:n] do
    let x := a * (2 * a - 1)
    if 40755 < x && ts.contains x && ps.contains x then
      return x
  return 0

end PE.P45
