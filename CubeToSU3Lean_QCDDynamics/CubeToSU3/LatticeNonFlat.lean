import CubeToSU3.LatticeGauge

/-!
# 非平庸的實例:用立方體自己的對稱造出有曲率的聯絡

`LatticeGauge` proved that a pure-gauge connection is flat.  That gives the word
"non-trivial" a meaning but no example: for all the file says, every connection
might be flat.  This file closes that by exhibiting one that is not.

Two steps, kept apart so that each stands on its own.

**The general fact.**  If two group elements fail to commute, the constant
connection built from them has a plaquette equal to their commutator, hence is
not flat, hence is not pure gauge in any frame.  This needs nothing about
`SU(3)` — it is true for any group — and its proof is a few rewrites.

**The instance.**  The two elements are taken from the cube's own symmetry
group, which is what makes this more than an existence statement:

* `Pmat` is the cyclic permutation of the coordinates — the 120° rotation about
  the 乾-坤 body diagonal, the very map `QianKunAxis.rotP` acts by, and the one
  whose infinitesimal generator is `Core.D`;
* `Smat = diag(1, -1, -1)` is a sign flip, an element of the `(Z/2)³` factor of
  `Aut(Q₃)` with determinant `+1`.

Both are real orthogonal with determinant one, hence lie in `SU(3)`.  They do
not commute — conjugating a diagonal matrix by a permutation permutes its
entries — and their commutator is

    W = P S P⁻¹ S⁻¹ = diag(-1, -1, 1)

with trace `-1` rather than `3`.  So the plaquette is non-trivial, the
connection carries curvature, and no choice of gauge removes it.

The geometric reading: transport a colour vector around one face of the cube
using the cube's own rotations, and it comes back rotated.  That rotation is the
lattice form of curvature, and it is exactly what `LatticeGauge` showed to be
gauge invariant in trace.

Nothing here is a physical claim.

**角色須知:這裡的立方體是底空間,不是內部結構。**

專案其他地方(`QianKunAxis`、`RootMatch`、`Weyl`、`WeylReal`)把立方體當作
**纖維側的內部結構**:三個爻是 `su(3)` 的三個色方向,乾坤軸挑出一個 Cartan
方向,六個非軸頂點是 `A₂` 的六個根,`S₄` 是 `SU(3)` 的一個特選有限子群。那一
側和時空毫無關係。

本檔案反過來,把 `Q₃` 當作**底空間**——每條有向稜掛一個群元素,繞一個面走一
圈。在纖維叢的語言裡,底空間與纖維是兩個不能互換的角色,而這裡用的是前者。

所以這一塊是**格點規範理論的一個小示範**,不是「立方體的內部結構長出了曲率」。
它證明的定理都成立,而且格點規範理論本身是有意義的數學;但它不是
`QianKunAxis → RootMatch` 那條主線的自然延伸,讀者不該把兩者接在一起讀。

真正的格點規範理論用的是四維時空格子(`32⁴` 以上),而 `Q₃` 是三維的八個點,
既不是時空、也裝不下任何強子。這裡不做任何物理計算的宣稱。
-/

noncomputable section

open Matrix

namespace CubeToSU3.Lattice

open CubeToSU3 CubeToSU3.Continuous

/-! ## The general fact: non-commuting elements give curvature -/

/-- The constant connection: direction `0` carries `a`, direction `1` carries
    `b`, direction `2` carries the identity. -/
def constConn (a b : SU3) : Connection :=
  fun _ d => if d = 0 then a else if d = 1 then b else 1

/-- Its plaquette in the `(0,1)` plane is the group commutator. -/
theorem constConn_plaquette (a b : SU3) (v : Fin 8) :
    plaquette (constConn a b) v 0 1 = a * b * a⁻¹ * b⁻¹ := by
  unfold plaquette constConn
  norm_num

/-- **Non-commuting elements give a non-flat connection.**  True in any group;
    `SU(3)` plays no special role. -/
theorem constConn_not_flat (a b : SU3) (hab : a * b ≠ b * a) :
    ¬ IsFlat (constConn a b) := by
  intro hflat
  have h := hflat 0 0 1
  rw [constConn_plaquette] at h
  apply hab
  have h2 : a * b * a⁻¹ * b⁻¹ * b = 1 * b := by rw [h]
  simp only [inv_mul_cancel_right, one_mul] at h2
  have h3 : a * b * a⁻¹ * a = b * a := by rw [h2]
  simpa using h3

/-- Consequently it is not pure gauge in any frame. -/
theorem constConn_not_pureGauge (a b : SU3) (hab : a * b ≠ b * a) :
    ∀ g : LatticeGauge, constConn a b ≠ pureGauge g := by
  intro g hEq
  exact constConn_not_flat a b hab (hEq ▸ pureGauge_isFlat g)

/-! ## The instance: two symmetries of the cube -/

/-- The 120° rotation about the 乾-坤 diagonal, as a matrix. -/
def PmatM : M3C := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- A sign flip with determinant one. -/
def SmatM : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

theorem PmatM_mem : PmatM ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PmatM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · rw [Matrix.det_fin_three]
    norm_num [PmatM]

theorem SmatM_mem : SmatM ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SmatM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · rw [Matrix.det_fin_three]
    norm_num [SmatM]

/-- The rotation, as an element of `SU(3)`. -/
def Prot : SU3 := ⟨PmatM, PmatM_mem⟩

/-- The sign flip, as an element of `SU(3)`. -/
def Sflip : SU3 := ⟨SmatM, SmatM_mem⟩

/-- They do not commute: conjugating a diagonal matrix by a permutation
    permutes its entries, and these entries are not all equal. -/
theorem Prot_Sflip_ne : Prot * Sflip ≠ Sflip * Prot := by
  intro h
  have hc : (PmatM * SmatM) = (SmatM * PmatM) :=
    congrArg (fun A : SU3 => (A : M3C)) h
  have h00 := congrFun (congrFun hc 1) 0
  simp [PmatM, SmatM, Matrix.mul_apply, Fin.sum_univ_three] at h00
  -- `simp` reduces the entry comparison to `(1 : ℂ) = -1` but has no lemma
  -- ruling that out; characteristic zero is `norm_num`'s job.
  norm_num at h00

/-- **A concrete non-flat connection on the cube.** -/
theorem cubeConn_not_flat : ¬ IsFlat (constConn Prot Sflip) :=
  constConn_not_flat Prot Sflip Prot_Sflip_ne

/-- **And it is pure gauge in no frame at all.**  The curvature it carries
    cannot be removed by any choice of frame at the eight vertices. -/
theorem cubeConn_not_pureGauge :
    ∀ g : LatticeGauge, constConn Prot Sflip ≠ pureGauge g :=
  constConn_not_pureGauge Prot Sflip Prot_Sflip_ne

/-! ## Axiom audit -/

#print axioms constConn_plaquette
#print axioms constConn_not_flat
#print axioms constConn_not_pureGauge
#print axioms PmatM_mem
#print axioms SmatM_mem
#print axioms Prot_Sflip_ne
#print axioms cubeConn_not_flat
#print axioms cubeConn_not_pureGauge

end CubeToSU3.Lattice
