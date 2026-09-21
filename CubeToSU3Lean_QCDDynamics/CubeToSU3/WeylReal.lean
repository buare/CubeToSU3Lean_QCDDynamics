/-
  WeylReal.lean

  Mathlib completion of CubeToSU3.Weyl.

  This file turns the finite calculations of `Weyl.lean` into a group action:

    CubeSym = (Z/2Z)^3 semidirect S3,     |CubeSym| = 48.

  Signed permutation conjugation acts on the Gaussian lattice and on the
  continuous real Lie algebra su(3).  The action preserves the commutator.
  Its kernel is exactly the central pair {+I,-I}; consequently its image has
  exactly 24 elements.

  Scope: this is the finite Weyl/signed-permutation symmetry of su(3).  It is
  not a construction of a gauge field, Yang--Mills dynamics, quantisation, or
  QCD.
-/

import Mathlib
import CubeToSU3.Weyl
import CubeToSU3.CompactSU3Real

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators

namespace CubeToSU3

/-! ## 1. The six permutations form S3 -/

namespace Perm3

/-- Multiplication is chosen so that `permMat (s * t) = permMat s ∘ permMat t`. -/
def mul : Perm3 → Perm3 → Perm3
  | .id,   t     => t
  | s,     .id   => s
  | .s01,  .s01  => .id
  | .s01,  .s02  => .c012
  | .s01,  .s12  => .c021
  | .s01,  .c012 => .s02
  | .s01,  .c021 => .s12
  | .s02,  .s01  => .c021
  | .s02,  .s02  => .id
  | .s02,  .s12  => .c012
  | .s02,  .c012 => .s12
  | .s02,  .c021 => .s01
  | .s12,  .s01  => .c012
  | .s12,  .s02  => .c021
  | .s12,  .s12  => .id
  | .s12,  .c012 => .s01
  | .s12,  .c021 => .s02
  | .c012, .s01  => .s12
  | .c012, .s02  => .s01
  | .c012, .s12  => .s02
  | .c012, .c012 => .c021
  | .c012, .c021 => .id
  | .c021, .s01  => .s02
  | .c021, .s02  => .s12
  | .c021, .s12  => .s01
  | .c021, .c012 => .id
  | .c021, .c021 => .c012

def inv : Perm3 → Perm3
  | .id   => .id
  | .s01  => .s01
  | .s02  => .s02
  | .s12  => .s12
  | .c012 => .c021
  | .c021 => .c012

instance : Group Perm3 where
  mul := mul
  one := .id
  inv := inv
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  inv_mul_cancel := by intro a; cases a <;> rfl

def equivFin6 : Perm3 ≃ Fin 6 where
  toFun
    | .id   => 0
    | .s01  => 1
    | .s02  => 2
    | .s12  => 3
    | .c012 => 4
    | .c021 => 5
  invFun i := ![.id, .s01, .s02, .s12, .c012, .c021] i
  left_inv := by intro s; cases s <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

instance : Fintype Perm3 :=
  Fintype.ofEquiv (Fin 6) equivFin6.symm

/-- The `Fintype` instance is built from `equivFin6`, so the cardinality is
    transported rather than computed. -/
theorem card : Fintype.card Perm3 = 6 :=
  (Fintype.card_congr equivFin6).trans (Fintype.card_fin 6)

/-- The actual permutation of the three coordinate indices. -/
def index : Perm3 → Fin 3 → Fin 3
  | .id,   i => i
  | .s01,  i => ![1, 0, 2] i
  | .s02,  i => ![2, 1, 0] i
  | .s12,  i => ![0, 2, 1] i
  | .c012, i => ![1, 2, 0] i
  | .c021, i => ![2, 0, 1] i

def equiv (s : Perm3) : Equiv.Perm (Fin 3) where
  toFun := index s
  invFun := index s⁻¹
  left_inv := by
    intro i
    cases s <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    cases s <;> fin_cases i <;> rfl

/-- The six constructors, as a homomorphism to the permutation group. -/
def toS3 : Perm3 →* Equiv.Perm (Fin 3) where
  -- `permMat` is a conjugation action, so its raw index maps compose in the
  -- opposite order.  Taking the inverse gives an honest homomorphism to S3.
  toFun s := equiv s⁻¹
  map_one' := by ext i; rfl
  map_mul' := by
    intro s t
    ext i
    cases s <;> cases t <;> fin_cases i <;> rfl

theorem toS3_injective : Function.Injective toS3 := by
  intro s t
  cases s <;> cases t <;> decide

theorem toS3_bijective : Function.Bijective toS3 := by
  apply (Fintype.bijective_iff_injective_and_card toS3).2
  constructor
  · exact toS3_injective
  · have hp : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      decide
    rw [card, hp]

/-- The six constructors are group-isomorphic to the full symmetric group S3. -/
noncomputable def equivS3 : Perm3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective toS3 toS3_bijective

end Perm3

theorem permMat_mul (s t : Perm3) (X : MatG3) :
    permMat (s * t) X = permMat s (permMat t X) := by
  cases s <;> cases t <;> rfl

/-! ## 2. The sign group (Z/2Z)^3 -/

inductive AxisSign where
  | pos | neg
deriving DecidableEq, Repr, Fintype

namespace AxisSign

def mul : AxisSign → AxisSign → AxisSign
  | .pos, b => b
  | .neg, .pos => .neg
  | .neg, .neg => .pos

instance : Group AxisSign where
  mul := mul
  one := .pos
  inv a := a
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  inv_mul_cancel := by intro a; cases a <;> rfl

def toInt : AxisSign → Int
  | .pos => 1
  | .neg => -1

def toReal : AxisSign → ℝ
  | .pos => 1
  | .neg => -1

@[simp] theorem toInt_mul (a b : AxisSign) : toInt (a * b) = toInt a * toInt b := by
  cases a <;> cases b <;> decide

@[simp] theorem toInt_sq (a : AxisSign) : toInt a * toInt a = 1 := by
  cases a <;> decide

@[simp] theorem toInt_pow_two (a : AxisSign) : toInt a ^ 2 = 1 := by
  simpa [pow_two] using toInt_sq a

@[simp] theorem toReal_mul (a b : AxisSign) : toReal (a * b) = toReal a * toReal b := by
  change toReal (AxisSign.mul a b) = toReal a * toReal b
  cases a <;> cases b <;> norm_num [toReal, AxisSign.mul]

@[simp] theorem toReal_sq (a : AxisSign) : toReal a * toReal a = 1 := by
  cases a <;> norm_num [toReal]

end AxisSign

structure Sign3 where
  e0 : AxisSign
  e1 : AxisSign
  e2 : AxisSign
deriving DecidableEq, Repr, Fintype

namespace Sign3

@[ext] theorem ext_fields {a b : Sign3}
    (h0 : a.e0 = b.e0) (h1 : a.e1 = b.e1) (h2 : a.e2 = b.e2) : a = b := by
  cases a
  cases b
  simp_all

def mul (a b : Sign3) : Sign3 := ⟨a.e0 * b.e0, a.e1 * b.e1, a.e2 * b.e2⟩
def one : Sign3 := ⟨1, 1, 1⟩
def inv (a : Sign3) : Sign3 := a

instance : Group Sign3 where
  mul := mul
  one := one
  inv := inv
  mul_assoc := by
    intro a b c
    change mul (mul a b) c = mul a (mul b c)
    apply ext_fields
    · exact _root_.mul_assoc _ _ _
    · exact _root_.mul_assoc _ _ _
    · exact _root_.mul_assoc _ _ _
  one_mul := by
    intro a
    change mul one a = a
    rfl
  mul_one := by
    intro a
    change mul a one = a
    apply ext_fields
    · exact _root_.mul_one _
    · exact _root_.mul_one _
    · exact _root_.mul_one _
  inv_mul_cancel := by
    intro a
    change mul (inv a) a = one
    rcases a with ⟨a0, a1, a2⟩
    cases a0 <;> cases a1 <;> cases a2 <;> rfl

theorem card : Fintype.card Sign3 = 8 := by decide

def allNeg : Sign3 := ⟨.neg, .neg, .neg⟩

def coord (e : Sign3) : Fin 3 → AxisSign := ![e.e0, e.e1, e.e2]

end Sign3

/-- Permuting the three sign coordinates. -/
def permSign : Perm3 → Sign3 → Sign3
  | .id,   e => e
  | .s01,  e => ⟨e.e1, e.e0, e.e2⟩
  | .s02,  e => ⟨e.e2, e.e1, e.e0⟩
  | .s12,  e => ⟨e.e0, e.e2, e.e1⟩
  | .c012, e => ⟨e.e1, e.e2, e.e0⟩
  | .c021, e => ⟨e.e2, e.e0, e.e1⟩

def permSignAut (s : Perm3) : Sign3 ≃* Sign3 where
  toFun := permSign s
  invFun := permSign s⁻¹
  left_inv := by
    intro e
    cases e with
    | mk e0 e1 e2 => cases s <;> rfl
  right_inv := by
    intro e
    cases e with
    | mk e0 e1 e2 => cases s <;> rfl
  map_mul' := by
    intro a b
    cases a with
    | mk a0 a1 a2 =>
      cases b with
      | mk b0 b1 b2 => cases s <;> rfl

theorem permSign_mul (s t : Perm3) (e : Sign3) :
    permSign (s * t) e = permSign s (permSign t e) := by
  rcases e with ⟨e0, e1, e2⟩
  cases s <;> cases t <;> rfl

def permSignAction : Perm3 →* MulAut Sign3 where
  toFun := permSignAut
  map_one' := by ext e <;> rfl
  map_mul' := by
    intro s t
    apply DFunLike.ext _ _
    intro e
    exact permSign_mul s t e

/-! ## 3. The 48-element semidirect product -/

abbrev CubeSym := Sign3 ⋊[permSignAction] Perm3

instance : Fintype CubeSym :=
  Fintype.ofEquiv (Sign3 × Perm3) SemidirectProduct.equivProd.symm

/-- `48 = 8 x 6` by transport along `SemidirectProduct.equivProd`; no
    enumeration of the group is needed. -/
theorem cubeSym_card : Fintype.card CubeSym = 48 := by
  have h : Fintype.card CubeSym = Fintype.card (Sign3 × Perm3) :=
    Fintype.card_congr SemidirectProduct.equivProd
  rw [h, Fintype.card_prod, Sign3.card, Perm3.card]

/-! ## 4. Integral action and preservation of the Lie bracket -/

def signAct3 (e : Sign3) (X : MatG3) : MatG3 :=
  signAct e.e0.toInt e.e1.toInt e.e2.toInt X

theorem signAct3_one (X : MatG3) : signAct3 1 X = X := by
  change signAct3 Sign3.one X = X
  cases X
  simp [signAct3, Sign3.one, signAct, gsmul, AxisSign.toInt]

theorem signAct3_mul (e f : Sign3) (X : MatG3) :
    signAct3 (e * f) X = signAct3 e (signAct3 f X) := by
  change signAct3 (Sign3.mul e f) X = signAct3 e (signAct3 f X)
  rcases e with ⟨e0, e1, e2⟩
  rcases f with ⟨f0, f1, f2⟩
  cases X
  simp [signAct3, Sign3.mul, signAct, gsmul,
    MatG3.mk.injEq, GInt.mk.injEq,
    AxisSign.toInt_mul, AxisSign.toInt_pow_two] <;>
    ring_nf <;> simp

theorem permMat_signAct3 (s : Perm3) (e : Sign3) (X : MatG3) :
    permMat s (signAct3 e X) = signAct3 (permSign s e) (permMat s X) := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases s <;> rfl

def cubeAct (g : CubeSym) (X : MatG3) : MatG3 :=
  signAct3 g.left (permMat g.right X)

theorem cubeAct_one (X : MatG3) : cubeAct 1 X = X := by
  change signAct3 Sign3.one X = X
  exact signAct3_one X

theorem cubeAct_mul (g h : CubeSym) (X : MatG3) :
    cubeAct (g * h) X = cubeAct g (cubeAct h X) := by
  rcases g with ⟨e, s⟩
  rcases h with ⟨f, t⟩
  change signAct3 (e * permSign s f) (permMat (s * t) X) =
    signAct3 e (permMat s (signAct3 f (permMat t X)))
  rw [permMat_mul, signAct3_mul, ← permMat_signAct3]

instance cubeSymMulActionMatG3 : MulAction CubeSym MatG3 where
  smul := cubeAct
  one_smul := cubeAct_one
  mul_smul := cubeAct_mul

theorem permMat_matmul (s : Perm3) (A B : MatG3) :
    permMat s (MatG3.mul A B) = MatG3.mul (permMat s A) (permMat s B) := by
  cases s <;> cases A <;> cases B <;>
    simp [permMat, MatG3.mul, GInt.add, GInt.mul,
      MatG3.mk.injEq, GInt.mk.injEq] <;> ring_nf <;> simp

theorem permMat_sub (s : Perm3) (A B : MatG3) :
    permMat s (MatG3.sub A B) = MatG3.sub (permMat s A) (permMat s B) := by
  cases s <;> cases A <;> cases B <;> rfl

theorem signAct3_matmul (e : Sign3) (A B : MatG3) :
    signAct3 e (MatG3.mul A B) = MatG3.mul (signAct3 e A) (signAct3 e B) := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases A <;> cases B <;>
    simp [signAct3, signAct, gsmul, MatG3.mul, GInt.add, GInt.mul,
      MatG3.mk.injEq, GInt.mk.injEq, AxisSign.toInt] <;>
    ring_nf <;> simp

theorem signAct3_neg (e : Sign3) (X : MatG3) :
    signAct3 e (MatG3.neg X) = MatG3.neg (signAct3 e X) := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases X <;>
    simp [signAct3, signAct, gsmul, MatG3.neg,
      GInt.neg, MatG3.mk.injEq, GInt.mk.injEq, AxisSign.toInt] <;>
    ring_nf <;> simp

theorem permMat_bracket (s : Perm3) (A B : MatG3) :
    permMat s (MatG3.bracket A B) =
      MatG3.bracket (permMat s A) (permMat s B) := by
  rw [MatG3.bracket, permMat_sub, permMat_matmul, permMat_matmul]
  rfl

theorem signAct3_bracket (e : Sign3) (A B : MatG3) :
    signAct3 e (MatG3.bracket A B) =
      MatG3.bracket (signAct3 e A) (signAct3 e B) := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases A <;> cases B <;>
    simp [signAct3, signAct, gsmul, MatG3.bracket, MatG3.sub,
      MatG3.mul, GInt.add, GInt.sub, GInt.neg, GInt.mul,
      MatG3.mk.injEq, GInt.mk.injEq, AxisSign.toInt] <;>
    ring_nf <;> simp

theorem cubeAct_bracket (g : CubeSym) (A B : MatG3) :
    cubeAct g (MatG3.bracket A B) =
      MatG3.bracket (cubeAct g A) (cubeAct g B) := by
  simp only [cubeAct, permMat_bracket, signAct3_bracket]

theorem signAct3_conjTranspose (e : Sign3) (X : MatG3) :
    MatG3.conjTranspose (signAct3 e X) =
      signAct3 e (MatG3.conjTranspose X) := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases X <;>
    simp [signAct3, signAct, gsmul, MatG3.conjTranspose,
      GInt.conj, MatG3.mk.injEq, GInt.mk.injEq, AxisSign.toInt] <;>
    ring_nf <;> simp

theorem signAct3_trace (e : Sign3) (X : MatG3) :
    MatG3.trace (signAct3 e X) = MatG3.trace X := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases X <;>
    simp [signAct3, signAct, gsmul, MatG3.trace, GInt.add,
      MatG3.mk.injEq, GInt.mk.injEq, AxisSign.toInt] <;>
    ring_nf <;> simp

theorem signAct3_mem {X : MatG3} (e : Sign3) (hX : IsSu3Alg X) :
    IsSu3Alg (signAct3 e X) := by
  constructor
  · rw [signAct3_conjTranspose, hX.1, signAct3_neg]
  · rw [signAct3_trace, hX.2]

theorem cubeAct_mem {X : MatG3} (g : CubeSym) (hX : IsSu3Alg X) :
    IsSu3Alg (cubeAct g X) :=
  signAct3_mem g.left (permMat_mem g.right hX)

/-! ## 5. The kernel is exactly {+I,-I} -/

def centralNeg : CubeSym := ⟨Sign3.allNeg, 1⟩

theorem cubeAct_centralNeg (X : MatG3) : cubeAct centralNeg X = X := by
  simpa [cubeAct, centralNeg, signAct3, Sign3.allNeg] using
    signAct_flip_all_trivial X

def cubeSignature (g : CubeSym) : MatG3 × MatG3 :=
  (cubeAct g testW, cubeAct g testS)

theorem signature_kernel_iff (g : CubeSym) :
    cubeSignature g = cubeSignature 1 ↔ g = 1 ∨ g = centralNeg := by
  rcases g with ⟨⟨e0, e1, e2⟩, s⟩
  cases e0 <;> cases e1 <;> cases e2 <;> cases s <;> decide

def ActsTrivially (g : CubeSym) : Prop := ∀ X : MatG3, cubeAct g X = X

theorem cube_kernel_iff (g : CubeSym) :
    ActsTrivially g ↔ g = 1 ∨ g = centralNeg := by
  constructor
  · intro h
    apply (signature_kernel_iff g).mp
    apply Prod.ext
    · simpa [cubeSignature, cubeAct_one] using h testW
    · simpa [cubeSignature, cubeAct_one] using h testS
  · rintro (rfl | rfl)
    · exact cubeAct_one
    · exact cubeAct_centralNeg

def actionKernel : Set CubeSym := {g | ActsTrivially g}

theorem actionKernel_eq : actionKernel = ({1, centralNeg} : Set CubeSym) := by
  ext g
  simp [actionKernel, cube_kernel_iff]

/-! ## 6. The action image has exactly 24 elements -/

/-- Two test matrices form a complete finite signature for these actions. -/
theorem signature_complete (g h : CubeSym) :
    cubeSignature g = cubeSignature h ↔
      ∀ X : MatG3, cubeAct g X = cubeAct h X := by
  constructor
  · intro hs
    have hw := congrArg (cubeAct g⁻¹) (congrArg Prod.fst hs)
    have hz := congrArg (cubeAct g⁻¹) (congrArg Prod.snd hs)
    have hrel : cubeSignature (g⁻¹ * h) = cubeSignature 1 := by
      apply Prod.ext
      · simpa [cubeSignature, ← cubeAct_mul, cubeAct_one] using hw.symm
      · simpa [cubeSignature, ← cubeAct_mul, cubeAct_one] using hz.symm
    have htriv : ActsTrivially (g⁻¹ * h) :=
      (cube_kernel_iff (g⁻¹ * h)).2 ((signature_kernel_iff (g⁻¹ * h)).1 hrel)
    intro X
    calc
      cubeAct g X = cubeAct g (cubeAct (g⁻¹ * h) X) := by rw [htriv X]
      _ = cubeAct (g * (g⁻¹ * h)) X := (cubeAct_mul _ _ _).symm
      _ = cubeAct h X := by simp
  · intro h
    apply Prod.ext <;> simp [cubeSignature, h]

/-- The finite image, represented by the complete two-matrix signature. -/
def actionImage : Finset (MatG3 × MatG3) :=
  Finset.univ.image cubeSignature

/-! The one genuinely computational step: the image of the 48 group elements
under the two-matrix signature has 24 distinct values.  Run in the kernel rather
than by compiled code, so the axiom footprint stays at
`propext / Classical.choice / Quot.sound`.  A doc comment cannot sit between
`set_option ... in` and the declaration it modifies, hence the module comment. -/

set_option maxRecDepth 40000 in
theorem actionImage_card : actionImage.card = 24 := by decide

theorem cube_48_kernel_2_image_24 :
    Fintype.card CubeSym = 48 ∧
    actionKernel = ({1, centralNeg} : Set CubeSym) ∧
    actionImage.card = 24 :=
  ⟨cubeSym_card, actionKernel_eq, actionImage_card⟩

/-! ## 7. Extension to the continuous real Lie algebra su(3) -/

namespace Continuous

def permMatR (s : Perm3) (X : M3C) : M3C :=
  fun i j => X (Perm3.index s i) (Perm3.index s j)

def signActR (e : Sign3) (X : M3C) : M3C :=
  fun i j =>
    ((e.coord i).toReal : ℂ) * X i j * ((e.coord j).toReal : ℂ)

def cubeActR (g : CubeSym) (X : M3C) : M3C :=
  signActR g.left (permMatR g.right X)

theorem permMatR_one (X : M3C) : permMatR 1 X = X := by
  ext i j
  rfl

theorem permMatR_mul (s t : Perm3) (X : M3C) :
    permMatR (s * t) X = permMatR s (permMatR t X) := by
  ext i j
  cases s <;> cases t <;> fin_cases i <;> fin_cases j <;> rfl

theorem signActR_one (X : M3C) : signActR 1 X = X := by
  change signActR Sign3.one X = X
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signActR, Sign3.coord, Sign3.one, AxisSign.toReal]

theorem signActR_mul (e f : Sign3) (X : M3C) :
    signActR (e * f) X = signActR e (signActR f X) := by
  change signActR (Sign3.mul e f) X = signActR e (signActR f X)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signActR, Sign3.coord, Sign3.mul,
      AxisSign.toReal_mul] <;> ring

theorem permMatR_signActR (s : Perm3) (e : Sign3) (X : M3C) :
    permMatR s (signActR e X) =
      signActR (permSign s e) (permMatR s X) := by
  ext i j
  rcases e with ⟨e0, e1, e2⟩
  cases s <;> fin_cases i <;> fin_cases j <;> rfl

theorem cubeActR_one (X : M3C) : cubeActR 1 X = X := by
  change signActR Sign3.one (permMatR Perm3.id X) = X
  calc
    signActR Sign3.one (permMatR Perm3.id X) = signActR Sign3.one X := by rfl
    _ = X := signActR_one X

theorem cubeActR_mul (g h : CubeSym) (X : M3C) :
    cubeActR (g * h) X = cubeActR g (cubeActR h X) := by
  rcases g with ⟨e, s⟩
  rcases h with ⟨f, t⟩
  change signActR (e * permSign s f) (permMatR (s * t) X) =
    signActR e (permMatR s (signActR f (permMatR t X)))
  rw [permMatR_mul, signActR_mul, ← permMatR_signActR]

theorem permMatR_conjTranspose (s : Perm3) (X : M3C) :
    (permMatR s X)ᴴ = permMatR s Xᴴ := by
  ext i j
  cases s <;> fin_cases i <;> fin_cases j <;>
    rfl

theorem permMatR_trace (s : Perm3) (X : M3C) :
    Matrix.trace (permMatR s X) = Matrix.trace X := by
  cases s <;>
    simp [permMatR, Perm3.index, Matrix.trace, Fin.sum_univ_succ] <;> ring

theorem signActR_conjTranspose (e : Sign3) (X : M3C) :
    (signActR e X)ᴴ = signActR e Xᴴ := by
  ext i j
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [signActR, Sign3.coord, AxisSign.toReal,
      Matrix.conjTranspose_apply] <;> ring_nf <;> simp

theorem signActR_trace (e : Sign3) (X : M3C) :
    Matrix.trace (signActR e X) = Matrix.trace X := by
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;>
    simp [signActR, Sign3.coord, AxisSign.toReal,
      Matrix.trace, Fin.sum_univ_succ] <;> ring_nf <;> simp

theorem permMatR_neg (s : Perm3) (X : M3C) :
    permMatR s (-X) = -permMatR s X := by rfl

theorem signActR_neg (e : Sign3) (X : M3C) :
    signActR e (-X) = -signActR e X := by
  ext i j
  simp [signActR] <;> ring_nf

theorem permMatR_mem {X : M3C} (s : Perm3) (hX : IsSu3R X) :
    IsSu3R (permMatR s X) := by
  constructor
  · rw [permMatR_conjTranspose, hX.1, permMatR_neg]
  · rw [permMatR_trace, hX.2]

theorem signActR_mem {X : M3C} (e : Sign3) (hX : IsSu3R X) :
    IsSu3R (signActR e X) := by
  constructor
  · rw [signActR_conjTranspose, hX.1, signActR_neg]
  · rw [signActR_trace, hX.2]

theorem cubeActR_mem {X : M3C} (g : CubeSym) (hX : IsSu3R X) :
    IsSu3R (cubeActR g X) :=
  signActR_mem g.left (permMatR_mem g.right hX)

theorem permMatR_matmul (s : Perm3) (A B : M3C) :
    permMatR s (A * B) = permMatR s A * permMatR s B := by
  ext i j
  cases s <;> fin_cases i <;> fin_cases j <;>
    simp [permMatR, Perm3.index, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem signActR_matmul (e : Sign3) (A B : M3C) :
    signActR e (A * B) = signActR e A * signActR e B := by
  ext i j
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [signActR, Sign3.coord, AxisSign.toReal,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp

theorem permMatR_bracket (s : Perm3) (A B : M3C) :
    permMatR s (bracketR A B) = bracketR (permMatR s A) (permMatR s B) := by
  ext i j
  cases s <;> fin_cases i <;> fin_cases j <;>
    simp [bracketR, permMatR, Perm3.index, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

theorem signActR_bracket (e : Sign3) (A B : M3C) :
    signActR e (bracketR A B) = bracketR (signActR e A) (signActR e B) := by
  ext i j
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [bracketR, signActR, Sign3.coord, AxisSign.toReal,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp

theorem cubeActR_bracket (g : CubeSym) (A B : M3C) :
    cubeActR g (bracketR A B) = bracketR (cubeActR g A) (cubeActR g B) := by
  simp only [cubeActR, permMatR_bracket, signActR_bracket]

theorem cubeActR_add (g : CubeSym) (A B : M3C) :
    cubeActR g (A + B) = cubeActR g A + cubeActR g B := by
  ext i j
  simp [cubeActR, signActR, permMatR] <;> ring

theorem cubeActR_smul (g : CubeSym) (r : ℝ) (A : M3C) :
    cubeActR g (r • A) = r • cubeActR g A := by
  ext i j
  simp [cubeActR, signActR, permMatR, smul_eq_mul] <;> ring

/-- The continuous action restricted to the real vector space `su(3)`. -/
def cubeActSu3R (g : CubeSym) (X : Su3R) : Su3R :=
  ⟨cubeActR g X.1, cubeActR_mem g X.2⟩

theorem cubeActSu3R_one (X : Su3R) : cubeActSu3R 1 X = X := by
  apply Subtype.ext
  exact cubeActR_one X.1

theorem cubeActSu3R_mul (g h : CubeSym) (X : Su3R) :
    cubeActSu3R (g * h) X = cubeActSu3R g (cubeActSu3R h X) := by
  apply Subtype.ext
  exact cubeActR_mul g h X.1

instance cubeSymMulActionSu3R : MulAction CubeSym Su3R where
  smul := cubeActSu3R
  one_smul := cubeActSu3R_one
  mul_smul := cubeActSu3R_mul

/-- Every cube symmetry acts by a real-linear automorphism of continuous
    `su(3)`, not merely by a set map. -/
def cubeActSu3LinearEquiv (g : CubeSym) : Su3R ≃ₗ[ℝ] Su3R where
  toFun := cubeActSu3R g
  invFun := cubeActSu3R g⁻¹
  left_inv := by
    intro X
    apply Subtype.ext
    calc
      cubeActR g⁻¹ (cubeActR g X.1) = cubeActR (g⁻¹ * g) X.1 :=
        (cubeActR_mul _ _ _).symm
      _ = X.1 := by simp [cubeActR_one]
  right_inv := by
    intro X
    apply Subtype.ext
    calc
      cubeActR g (cubeActR g⁻¹ X.1) = cubeActR (g * g⁻¹) X.1 :=
        (cubeActR_mul _ _ _).symm
      _ = X.1 := by simp [cubeActR_one]
  map_add' := by
    intro A B
    apply Subtype.ext
    exact cubeActR_add g A.1 B.1
  map_smul' := by
    intro r A
    apply Subtype.ext
    exact cubeActR_smul g r A.1

/-- Entrywise complexification intertwines the lattice and continuous actions. -/
theorem complexify_permMat (s : Perm3) (X : MatG3) :
    complexifyMatG3 (permMat s X) = permMatR s (complexifyMatG3 X) := by
  ext i j
  cases s <;> fin_cases i <;> fin_cases j <;> rfl

theorem complexify_signAct3 (e : Sign3) (X : MatG3) :
    complexifyMatG3 (signAct3 e X) = signActR e (complexifyMatG3 X) := by
  ext i j
  rcases e with ⟨e0, e1, e2⟩
  cases e0 <;> cases e1 <;> cases e2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [complexifyMatG3, ofGInt, signAct3, signAct, gsmul,
      signActR, Sign3.coord, AxisSign.toInt, AxisSign.toReal,
      Complex.ext_iff] <;> ring_nf <;> simp

theorem complexify_cubeAct (g : CubeSym) (X : MatG3) :
    complexifyMatG3 (cubeAct g X) = cubeActR g (complexifyMatG3 X) := by
  rw [cubeAct, cubeActR, complexify_signAct3, complexify_permMat]

end Continuous

/-! ## Axiom audit -/

#print axioms Perm3.equivS3
#print axioms cubeSym_card
#print axioms cubeAct_bracket
#print axioms cube_kernel_iff
#print axioms signature_complete
#print axioms actionImage_card
#print axioms Continuous.cubeActR_mem
#print axioms Continuous.cubeActR_bracket
#print axioms Continuous.cubeActSu3LinearEquiv
#print axioms Continuous.complexify_cubeAct

end CubeToSU3
