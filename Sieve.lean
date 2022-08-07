namespace Nat

theorem lt_add_of_pos_right (h : 0 < b) a : a < a + b := Nat.add_lt_add_left h ..

theorem sub_lt_sub_left {a b c : Nat} (hb : a < b) (hc : a < c) : c - b < c - a := by
  induction c generalizing a b with
  | zero => contradiction
  | succ c ihc => cases b with
    | zero => contradiction
    | succ b => cases a with simp only [Nat.succ_sub_succ]
      | zero => exact trans (show c - b ≤ c from Nat.sub_le ..) (show c < c.succ from Nat.le_refl ..)
      | succ a => exact ihc (Nat.lt_of_succ_lt_succ hb) (Nat.lt_of_succ_lt_succ hc)

theorem add_mod_right (a b : Nat) : (a + b) % b = a % b := by
  rw [mod_eq_sub_mod (Nat.le_add_left ..), Nat.add_sub_assoc (Nat.le_refl ..), Nat.sub_self, Nat.add_zero]

theorem add_mod_left (a b : Nat) : (a + b) % a = b % a := by
  rw [Nat.add_comm, add_mod_right]

end Nat

namespace Fin

theorem isLe (a : Fin n) : a ≤ n := Nat.le_of_lt a.isLt

theorem val_add_eq (a b : Fin n) : (a + b).val = (a.val + b.val) % n := rfl

theorem val_add_eq_of_lt_size {a b : Fin n} (h : a.val + b.val < n) : (a + b).val = a.val + b.val := by
  rw [val_add_eq, Nat.mod_eq_of_lt h]

theorem val_sub_eq (a b : Fin n) : (a - b).val = (a.val + (n - b.val)) % n := rfl

theorem val_sub_eq' (a b : Fin n) : (a - b).val = (a.val + n - b.val) % n := by
  rw [val_sub_eq, ←Nat.add_sub_assoc b.isLe]

theorem val_sub_eq_of_le_val {a b : Fin n} (h : b.val ≤ a.val) : (a - b).val = a.val - b.val := by
  have : a.val - b.val < n := trans (Nat.sub_le ..) a.isLt
  rw [val_sub_eq', Nat.add_comm, Nat.add_sub_assoc h, Nat.add_mod_left, Nat.mod_eq_of_lt this]

theorem val_mul_eq (a b : Fin n) : (a * b).val = (a.val * b.val) % n := rfl

theorem val_mul_eq_of_lt_size {a b : Fin n} (h : a.val * b.val < n) : (a * b).val = a.val * b.val := by
  rw [val_mul_eq, Nat.mod_eq_of_lt h]

theorem val_ofNat'_eq_of_lt (hn : n > 0) (hlt : a < n) : (Fin.ofNat' a hn).val = a := Nat.mod_eq_of_lt hlt

theorem val_lt_of_lt {a b : Fin n} (h : a < b) : a.val < b.val := h

theorem val_le_of_le {a b : Fin n} (h : a ≤ b) : a.val ≤ b.val := h

end Fin

namespace USize

theorem toNat_add_eq_of_le_toNat {a b c : USize} (h : a.toNat + b.toNat ≤ c.toNat) : (a + b).toNat = a.toNat + b.toNat :=
  Fin.val_add_eq_of_lt_size (trans h c.val.isLt)

theorem toNat_sub_eq_of_le_toNat {a b : USize} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := Fin.val_sub_eq_of_le_val h

theorem toNat_mul_eq_of_le_toNat {a b c : USize} (h : a.toNat * b.toNat ≤ c.toNat) : (a * b).toNat = a.toNat * b.toNat :=
  Fin.val_mul_eq_of_lt_size (trans h c.val.isLt)

theorem lt_size_of_lt (hlt : a < 4294967296) : a < USize.size := by
  cases usize_size_eq with rw [‹size = _›]
  | inl => exact hlt
  | inr => exact trans hlt (show 4294967296 < 18446744073709551616 by decide)

@[simp] theorem toNat_zero : (0 : USize).toNat = 0 :=
  Fin.val_ofNat'_eq_of_lt usize_size_gt_zero (lt_size_of_lt (by decide))

@[simp] theorem toNat_one : (1 : USize).toNat = 1 :=
  Fin.val_ofNat'_eq_of_lt usize_size_gt_zero (lt_size_of_lt (by decide))

theorem toNat_lt_of_lt {a b : USize} (h : a < b) : a.toNat < b.toNat := Fin.val_lt_of_lt h

theorem toNat_le_of_le {a b : USize} (h : a ≤ b) : a.toNat ≤ b.toNat := Fin.val_le_of_le h

end USize

namespace ByteArray

@[simp] theorem size_set (a : ByteArray) i v : (set a i v).size = a.size := Array.size_set ..

@[simp] theorem size_uset (a : ByteArray) i h v : (uset a i h v).size = a.size := Array.size_set ..

@[simp] theorem size_push (a : ByteArray) v : (push a v).size = a.size + 1 := Array.size_push ..

end ByteArray

namespace Sieve

-- `n` is the size of the current sieve.
-- `p` is a prime.
-- `m` is a multiple of `p`.
-- `bs` is the current table. `bs[x] = 0` means `x` is crossed out.

structure InnerInvariants (n : USize) (p : USize) (m : USize) (bs : ByteArray) : Prop where
  pGt : p.toNat > 0
  pLe : p.toNat ≤ n.toNat
  mLt : m.toNat < n.toNat
  sizeEq : bs.size = n.toNat

def inner (h : InnerInvariants n p m bs) : { bs : ByteArray // bs.size = n.toNat } :=
  have : m.toNat < bs.size := by rw [h.sizeEq]; apply h.mLt
  let bs := bs.uset m 0 this
  if hlt:m < n - p then
    have hkey : m.toNat + p.toNat < n.toNat := by
      apply Nat.add_lt_of_lt_sub
      rw [←USize.toNat_sub_eq_of_le_toNat h.pLe]
      exact hlt
    have _decreasing : n.toNat - (m + p).toNat < n.toNat - m.toNat := by
      have : m.toNat < (m + p).toNat := by
        rw [USize.toNat_add_eq_of_le_toNat (Nat.le_of_lt hkey)]
        apply Nat.lt_add_of_pos_right h.pGt
      exact Nat.sub_lt_sub_left this h.mLt
    @inner n p (m + p) bs { h with
      mLt := by
        rw [USize.toNat_add_eq_of_le_toNat (Nat.le_of_lt hkey)]
        exact hkey
      sizeEq := by rw [ByteArray.size_uset, h.sizeEq]
    }
  else
    have : bs.size = n.toNat := by rw [ByteArray.size_uset, h.sizeEq]
    ⟨bs, this⟩
termination_by inner n p m bs _ => n.toNat - m.toNat

structure LoopInvariants (n : USize) (sqrtn : USize) (p : USize) (bs : ByteArray) : Prop where
  pGt : p.toNat > 0
  sqrtnLt : sqrtn.toNat * sqrtn.toNat < n.toNat
  sqrtnLt' : sqrtn.toNat < n.toNat
  sizeEq : bs.size = n.toNat

def loop (h : LoopInvariants n sqrtn p bs) : ByteArray :=
  if hle:p ≤ sqrtn then
    have hpp : p.toNat * p.toNat < n.toNat := trans (Nat.mul_le_mul hle hle) h.sqrtnLt
    have pLt : p.toNat < n.toNat := trans (USize.toNat_le_of_le hle) h.sqrtnLt'
    let ⟨bs, sizeEq⟩ := @inner n p (p * p) bs { h with
      pLe := Nat.le_trans (USize.toNat_le_of_le hle) (Nat.le_of_lt h.sqrtnLt')
      mLt := by
        rw [USize.toNat_mul_eq_of_le_toNat (Nat.le_of_lt hpp)]
        exact hpp
    }
    have pLe' : p.toNat + (1 : USize).toNat ≤ n.toNat := by
      rw [USize.toNat_one, Nat.add_one]
      exact pLt
    have _decreasing : n.toNat - (p + 1).toNat < n.toNat - p.toNat := by
      apply Nat.sub_lt_sub_left _ pLt
      rw [USize.toNat_add_eq_of_le_toNat pLe', USize.toNat_one, Nat.add_one]
      apply Nat.lt_succ_self
    @loop n sqrtn (p + 1) bs { h with
      pGt := by
        rw [USize.toNat_add_eq_of_le_toNat pLe', USize.toNat_one]
        apply Nat.succ_pos
      sizeEq := sizeEq
    }
  else
    bs
termination_by loop n sqrtn p bs _ => n.toNat - p.toNat

def isqrtAux (n : Nat) (lo up : Nat) : Nat :=
  if up - lo > 1 then
    let x := lo + (up - lo) / 2
    have : up - x < up - lo := sorry
    have : x - lo < up - lo := sorry
    if x * x ≤ n then
      isqrtAux n x up
    else
      isqrtAux n lo x
  else
    lo
termination_by isqrtAux _ lo up => up - lo

def isqrt (n : Nat) := isqrtAux n 0 (n + 1)

def isqrt' (n : Nat) :=
  let s := isqrt n
  if s * s ≥ n then
    s - 1
  else
    s

def initArray (n : USize) (i : USize) (bs : ByteArray) (iLe : i.toNat ≤ n.toNat) (sizeEq : bs.size = i.toNat) : { bs : ByteArray // bs.size = n.toNat } :=
  if hlt:i < n then
    let bs := bs.push 1
    have iLe : (i + 1).toNat ≤ n.toNat := sorry
    have sizeEq : bs.size = (i + 1).toNat := sorry
    have : n.toNat - (i + 1).toNat < n.toNat - i.toNat := sorry
    initArray n (i + 1) bs iLe sizeEq
  else
    have : bs.size = n.toNat := sorry
    ⟨bs, this⟩
termination_by initArray n i bs _ _ => n.toNat - i.toNat

def sieve (n : USize) : ByteArray :=
  if h:n.toNat > 1 then    
    let bs := ByteArray.mkEmpty n.toNat
    let bs := bs.push 0
    let bs := bs.push 0
    let iLe : (2 : USize).toNat ≤ n.toNat := sorry
    let sizeEq : bs.size = (2 : USize).toNat := sorry
    let ⟨bs, sizeEq⟩ := initArray n 2 bs iLe sizeEq
    let sqrtn := isqrt' n.toNat
    let sqrtn := USize.ofNat sqrtn
    @loop n sqrtn 2 bs {
      pGt := sorry
      sqrtnLt := sorry
      sqrtnLt' := sorry
      sizeEq := sizeEq
    }
  else
    ByteArray.mk (mkArray n.toNat 0)

end Sieve

@[noinline] opaque blackBox : α → IO α := pure

def withTimeMeasured (f : α → β) (a : α) : IO (β × Nat) := do
  let startTime ← IO.monoMsNow
  let a ← blackBox a
  let b ← blackBox (f a)
  let endTime ← IO.monoMsNow
  return (b, endTime - startTime)

def main : IO Unit := do
  repeat
    let some n := (← (← IO.getStdin).getLine).trim.toNat? | break
    let (bs, time) ← withTimeMeasured Sieve.sieve (USize.ofNat n)
    let primeCount := bs.foldl (fun x b => if b != 0 then x + 1 else x) 0 (start := 2)
    println! "Prime count: {primeCount} ({time}ms)"
