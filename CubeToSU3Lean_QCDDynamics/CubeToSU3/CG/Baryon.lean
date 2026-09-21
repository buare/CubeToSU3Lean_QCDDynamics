import CubeToSU3.CG.Fundamental

/-!
# `3 ⊗ 3 ⊗ 3 = 10 ⊕ 8_S ⊕ 8_A ⊕ 1`

Coupling order `(3 ⊗ 3) ⊗ 3`, so the two octets are separated by the
permutation symmetry of the **first two** quarks, as in the standard treatment:

* `8_S ⊂ 6 ⊗ 3`   (symmetric in slots 1,2)
* `8_A ⊂ 3̄ ⊗ 3`   (antisymmetric in slots 1,2)

Unnormalised integer states, for labels `a b c`:

* `dec a b c = Σ_{σ ∈ S₃} |σ(abc)⟩`        — decuplet, totally symmetric
* `sing = ε`                               — singlet, totally antisymmetric
* `sS a b c = 3(|abc⟩ + |bac⟩) - dec a b c`
* `sA a b c = 3(|abc⟩ - |bac⟩) - ε_abc · sing`

Normalisation: e.g. `|Δ⁺⁺⟩ = dec u u u / 6`, `|Δ⁺⟩ = dec u u d / (3√3)`,
`|Σ*⁰⟩ = dec u d s / √6`, and the three-quark singlet is `sing / √6`.

What is proved, all by kernel evaluation over `Fin 3`:

1. `dec` is a totally symmetric tensor, `sing` is totally antisymmetric.
2. All four families are invariant subspaces (`*_closed`), stated for the nine
   matrix units, hence by linearity for all of `gl(3)` and `su(3)`.
3. `sing` carries the determinant: `act T sing = (tr T) · sing`, so it is
   invariant on `su(3)`.
4. The four families are mutually orthogonal.
5. Completeness: `6 |abc⟩ = dec + ε_abc · sing + sS + sA`,  i.e. `27 = 10+8+8+1`.
-/

set_option maxHeartbeats 4000000

namespace CubeToSU3.CG

/-- A vector in `3 ⊗ 3 ⊗ 3`. -/
abbrev Ten3 := Idx → Idx → Idx → Int

/-- Basis tensor `|abc⟩`. -/
def ket3 (a b c : Idx) : Ten3 :=
  fun i j k => delta i a * delta j b * delta k c

/-- Integer inner product. -/
def dot3 (x y : Ten3) : Int :=
  sum3 (fun i => sum3 (fun j => sum3 (fun k => x i j k * y i j k)))

/-- Action of `T` on `3 ⊗ 3 ⊗ 3`: `T⊗1⊗1 + 1⊗T⊗1 + 1⊗1⊗T`. -/
def act333 (T : Mat) (t : Ten3) : Ten3 :=
  fun i j k =>
    sum3 (fun m => T i m * t m j k)
      + sum3 (fun m => T j m * t i m k)
      + sum3 (fun m => T k m * t i j m)

/-! ## The four families -/

/-- Decuplet state: the sum over all six orderings of the labels. -/
def dec (a b c : Idx) : Ten3 :=
  fun i j k =>
    ket3 a b c i j k + ket3 a c b i j k + ket3 b a c i j k
      + ket3 b c a i j k + ket3 c a b i j k + ket3 c b a i j k

/-- The totally antisymmetric singlet, `√6 · |1⟩`. -/
def sing : Ten3 := fun i j k => eps i j k

/-- Octet state symmetric in the first two slots (`8_S ⊂ 6 ⊗ 3`). -/
def sS (a b c : Idx) : Ten3 :=
  fun i j k => 3 * (ket3 a b c i j k + ket3 b a c i j k) - dec a b c i j k

/-- Octet state antisymmetric in the first two slots (`8_A ⊂ 3̄ ⊗ 3`). -/
def sA (a b c : Idx) : Ten3 :=
  fun i j k => 3 * (ket3 a b c i j k - ket3 b a c i j k) - eps a b c * sing i j k

/-! ## 1. Permutation symmetry -/

theorem dec_symm_12 : ∀ a b c i j k : Idx, dec a b c i j k = dec a b c j i k := by decide
theorem dec_symm_23 : ∀ a b c i j k : Idx, dec a b c i j k = dec a b c i k j := by decide

/-- The decuplet depends only on the multiset of labels. -/
theorem dec_label_12 : ∀ a b c i j k : Idx, dec a b c i j k = dec b a c i j k := by decide
theorem dec_label_23 : ∀ a b c i j k : Idx, dec a b c i j k = dec a c b i j k := by decide

theorem sing_antisymm_12 : ∀ i j k : Idx, sing i j k = - sing j i k := by decide
theorem sing_antisymm_23 : ∀ i j k : Idx, sing i j k = - sing i k j := by decide

theorem sS_symm_12 : ∀ a b c i j k : Idx, sS a b c i j k = sS b a c i j k := by decide
theorem sA_antisymm_12 : ∀ a b c i j k : Idx, sA a b c i j k = - sA b a c i j k := by decide

/-! ## 2. Invariance of each family

For every matrix unit `E a b`, hence for every `T ∈ gl(3)`:

  `act T (X p q r) = Σ_m T_mp X m q r + Σ_m T_mq X p m r + Σ_m T_mr X p q m`. -/

theorem dec_closed :
    ∀ a b p q r i j k : Idx,
      act333 (E a b) (dec p q r) i j k
        = sum3 (fun m => E a b m p * dec m q r i j k)
          + sum3 (fun m => E a b m q * dec p m r i j k)
          + sum3 (fun m => E a b m r * dec p q m i j k) := by
  decide

theorem sS_closed :
    ∀ a b p q r i j k : Idx,
      act333 (E a b) (sS p q r) i j k
        = sum3 (fun m => E a b m p * sS m q r i j k)
          + sum3 (fun m => E a b m q * sS p m r i j k)
          + sum3 (fun m => E a b m r * sS p q m i j k) := by
  decide

theorem sA_closed :
    ∀ a b p q r i j k : Idx,
      act333 (E a b) (sA p q r) i j k
        = sum3 (fun m => E a b m p * sA m q r i j k)
          + sum3 (fun m => E a b m q * sA p m r i j k)
          + sum3 (fun m => E a b m r * sA p q m i j k) := by
  decide

/-! ## 3. The singlet carries the determinant -/

/-- `act T sing = (tr T) · sing`; on traceless `T`, i.e. on `su(3)`, the singlet
    is invariant.  This is `Λ³(3) ≅ det`. -/
theorem sing_action :
    ∀ a b i j k : Idx,
      act333 (E a b) sing i j k = trace (E a b) * sing i j k := by
  decide

theorem sing_invariant_offdiag :
    ∀ a b i j k : Idx, a ≠ b → act333 (E a b) sing i j k = 0 := by decide

theorem sing_invariant_H1 : ∀ i j k : Idx, act333 H1 sing i j k = 0 := by decide
theorem sing_invariant_H2 : ∀ i j k : Idx, act333 H2 sing i j k = 0 := by decide

/-! ## 4. Mutual orthogonality -/

theorem dec_perp_sing : ∀ a b c : Idx, dot3 (dec a b c) sing = 0 := by decide
theorem dec_perp_sS : ∀ a b c p q r : Idx, dot3 (dec a b c) (sS p q r) = 0 := by decide
theorem dec_perp_sA : ∀ a b c p q r : Idx, dot3 (dec a b c) (sA p q r) = 0 := by decide
theorem sing_perp_sS : ∀ p q r : Idx, dot3 sing (sS p q r) = 0 := by decide
theorem sing_perp_sA : ∀ p q r : Idx, dot3 sing (sA p q r) = 0 := by decide
theorem sS_perp_sA : ∀ a b c p q r : Idx, dot3 (sS a b c) (sA p q r) = 0 := by decide

/-! ## 5. Completeness -/

/-- `6 |abc⟩ = dec + ε_abc · sing + sS + sA`.  With `27 = 10 + 8 + 8 + 1`,
    this is the decomposition `3 ⊗ 3 ⊗ 3 = 10 ⊕ 8_S ⊕ 8_A ⊕ 1`. -/
theorem completeness3 :
    ∀ a b c i j k : Idx,
      6 * ket3 a b c i j k
        = dec a b c i j k + eps a b c * sing i j k
          + sS a b c i j k + sA a b c i j k := by
  decide

/-! ## Named states

`Δ⁺⁺ ∝ dec u u u`, `Δ⁺ ∝ dec u u d`, `Σ*⁰ ∝ dec u d s`, `Ω⁻ ∝ dec s s s`;
the proton-type octet states are `sS`/`sA` combinations of `u u d`. -/

theorem dec_uuu_norm : dot3 (dec u u u) (dec u u u) = 36 := by decide
theorem dec_uud_norm : dot3 (dec u u d) (dec u u d) = 12 := by decide
theorem dec_uds_norm : dot3 (dec u d s) (dec u d s) = 6 := by decide
theorem sing_norm : dot3 sing sing = 6 := by decide

/-- Three identical labels leave nothing in the octets or the singlet: there is
    no spin-1/2-type `uuu` state. -/
theorem sS_uuu_zero : ∀ i j k : Idx, sS u u u i j k = 0 := by decide
theorem sA_uuu_zero : ∀ i j k : Idx, sA u u u i j k = 0 := by decide
theorem sS_sss_zero : ∀ i j k : Idx, sS s s s i j k = 0 := by decide
theorem sA_sss_zero : ∀ i j k : Idx, sA s s s i j k = 0 := by decide

end CubeToSU3.CG
