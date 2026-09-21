import CubeToSU3.LatticeNonFlat

/-!
# Wilson 作用量:曲率變成一個數

`LatticeGauge` made the plaquette holonomy gauge covariant and its trace an
observable; `LatticeNonFlat` exhibited a connection whose holonomy is not `1`.
This file turns that into a number.

The Wilson action assigns to each face the quantity

    3 - Re tr W(face)

The `3` is `tr 1`, so the contribution vanishes exactly when the holonomy is
trivial and is otherwise positive.  Summing over the twenty-four
(vertex, plane) pairs of the cube — six faces, each counted once per corner —
gives a single real number attached to the connection.

Two facts make it an observable rather than an artefact of the frame:

* it is gauge invariant, which follows in one step from
  `trace_plaquette_gaugeAct`;
* it vanishes on pure-gauge connections, since every plaquette is then `1`.

And one computation makes it concrete.  For the connection of `LatticeNonFlat`,
built from the 120° rotation about the 乾-坤 diagonal and a sign flip, the
holonomy in the `(0,1)` plane is `diag(-1,-1,1)` with trace `-1`, while the
other two planes have holonomy `1` because direction `2` carries the identity.
Each vertex therefore contributes `3 - (-1) = 4`, and

    S = 8 × 4 = 32

This is the first non-zero gauge-invariant *number* in the project.  Everything
before it was either an identity, a vanishing no-go, or a matrix.

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

那個 `S = 32` 是這個示範格點上的一個位形的作用量,不是物理量:物理的作用量帶
著耦合前因子 `β`,而可觀測量是對所有位形的路徑積分平均,不是單一位形的值。
-/

noncomputable section

open Matrix

namespace CubeToSU3.Lattice

open CubeToSU3 CubeToSU3.Continuous

/-! ## The action -/

/-- The Wilson energy of one plaquette: `3 - Re tr W`. -/
def plaqEnergy (U : Connection) (v : Fin 8) (b c : Fin 3) : ℝ :=
  3 - (Matrix.trace ((plaquette U v b c : SU3) : M3C)).re

/-- The Wilson action: the three coordinate planes summed over the eight
    vertices.  Each of the cube's six faces is counted once per corner. -/
def wilsonAction (U : Connection) : ℝ :=
  ∑ v : Fin 8, (plaqEnergy U v 0 1 + plaqEnergy U v 0 2 + plaqEnergy U v 1 2)

/-! ## Gauge invariance -/

theorem plaqEnergy_gaugeAct (g : LatticeGauge) (U : Connection)
    (v : Fin 8) (b c : Fin 3) :
    plaqEnergy (gaugeAct g U) v b c = plaqEnergy U v b c := by
  unfold plaqEnergy
  rw [trace_plaquette_gaugeAct]

/-- **The Wilson action is an observable.**  It depends on the connection, not
    on the frame chosen at each vertex. -/
theorem wilsonAction_gaugeAct (g : LatticeGauge) (U : Connection) :
    wilsonAction (gaugeAct g U) = wilsonAction U := by
  unfold wilsonAction
  simp only [plaqEnergy_gaugeAct]

/-! ## Vanishing on flat connections -/

theorem plaqEnergy_of_plaquette_one (U : Connection) (v : Fin 8) (b c : Fin 3)
    (h : plaquette U v b c = 1) : plaqEnergy U v b c = 0 := by
  unfold plaqEnergy
  rw [h]
  show 3 - (Matrix.trace ((1 : M3C))).re = 0
  rw [Matrix.trace_one]
  norm_num

/-- A flat connection has zero action. -/
theorem wilsonAction_of_flat (U : Connection) (h : IsFlat U) :
    wilsonAction U = 0 := by
  unfold wilsonAction
  have h01 : ∀ v : Fin 8, plaqEnergy U v 0 1 = 0 :=
    fun v => plaqEnergy_of_plaquette_one U v 0 1 (h v 0 1)
  have h02 : ∀ v : Fin 8, plaqEnergy U v 0 2 = 0 :=
    fun v => plaqEnergy_of_plaquette_one U v 0 2 (h v 0 2)
  have h12 : ∀ v : Fin 8, plaqEnergy U v 1 2 = 0 :=
    fun v => plaqEnergy_of_plaquette_one U v 1 2 (h v 1 2)
  simp [h01, h02, h12]

theorem wilsonAction_pureGauge (g : LatticeGauge) :
    wilsonAction (pureGauge g) = 0 :=
  wilsonAction_of_flat _ (pureGauge_isFlat g)

/-! ## The concrete value -/

/-- The commutator, written out as a matrix.  Inverses in `SU(3)` are conjugate
    transposes, which is what `coe_su3_inv` supplies. -/
theorem cubeComm_coe :
    ((Prot * Sflip * Prot⁻¹ * Sflip⁻¹ : SU3) : M3C)
      = PmatM * SmatM * PmatMᴴ * SmatMᴴ := by
  show ((Prot : SU3) : M3C) * ((Sflip : SU3) : M3C)
      * ((Prot⁻¹ : SU3) : M3C) * ((Sflip⁻¹ : SU3) : M3C) = _
  rw [coe_su3_inv, coe_su3_inv]
  rfl

/-- The conjugate transposes, written out.  Both matrices are real, so these
    are plain transposes; computing them first keeps the product below from
    stalling on unevaluated entries. -/
theorem PmatM_conjTranspose : PmatMᴴ = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PmatM, Matrix.conjTranspose_apply]

theorem SmatM_conjTranspose : SmatMᴴ = SmatM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SmatM, Matrix.conjTranspose_apply]

/-- The commutator as an explicit matrix. -/
theorem cubeComm_matrix :
    PmatM * SmatM * PmatMᴴ * SmatMᴴ = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [PmatM_conjTranspose, SmatM_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PmatM, SmatM, Matrix.mul_apply, Fin.sum_univ_three]

theorem cubeComm_trace :
    Matrix.trace ((Prot * Sflip * Prot⁻¹ * Sflip⁻¹ : SU3) : M3C) = -1 := by
  rw [cubeComm_coe, cubeComm_matrix]
  simp [Matrix.trace_fin_three]

/-- The `(0,1)` plaquette of the cube connection has energy four. -/
theorem cubeConn_plaqEnergy_01 (v : Fin 8) :
    plaqEnergy (constConn Prot Sflip) v 0 1 = 4 := by
  unfold plaqEnergy
  rw [constConn_plaquette, cubeComm_trace]
  norm_num

/-- The other two planes are flat, because direction `2` carries the identity;
    the holonomy there is `a · 1 · a⁻¹ · 1 = 1`. -/
-- `simp` reduces `if (0 : Fin 3) = 0` on its own but stalls on
-- `if (2 : Fin 3) = 0`; supplying the two disequalities lets it discharge them.
theorem cubeConn_plaquette_02 (v : Fin 8) :
    plaquette (constConn Prot Sflip) v 0 2 = 1 := by
  have e0 : (2 : Fin 3) ≠ 0 := by decide
  have e1 : (2 : Fin 3) ≠ 1 := by decide
  simp [plaquette, constConn, e0, e1]

theorem cubeConn_plaquette_12 (v : Fin 8) :
    plaquette (constConn Prot Sflip) v 1 2 = 1 := by
  have e0 : (2 : Fin 3) ≠ 0 := by decide
  have e1 : (2 : Fin 3) ≠ 1 := by decide
  have e2 : (1 : Fin 3) ≠ 0 := by decide
  simp [plaquette, constConn, e0, e1, e2]

/-- **The first non-zero gauge-invariant number.**  No choice of frame at the
    eight vertices can lower it. -/
theorem cubeConn_wilsonAction :
    wilsonAction (constConn Prot Sflip) = 32 := by
  unfold wilsonAction
  have h02 : ∀ v : Fin 8, plaqEnergy (constConn Prot Sflip) v 0 2 = 0 :=
    fun v => plaqEnergy_of_plaquette_one _ v 0 2 (cubeConn_plaquette_02 v)
  have h12 : ∀ v : Fin 8, plaqEnergy (constConn Prot Sflip) v 1 2 = 0 :=
    fun v => plaqEnergy_of_plaquette_one _ v 1 2 (cubeConn_plaquette_12 v)
  simp [cubeConn_plaqEnergy_01, h02, h12]
  norm_num

/-- Hence it is not flat, recovered from the action rather than from the
    holonomy directly. -/
theorem cubeConn_not_flat' : ¬ IsFlat (constConn Prot Sflip) := by
  intro h
  have h0 := wilsonAction_of_flat _ h
  rw [cubeConn_wilsonAction] at h0
  norm_num at h0

/-! ## Axiom audit -/

#print axioms plaqEnergy_gaugeAct
#print axioms wilsonAction_gaugeAct
#print axioms wilsonAction_pureGauge
#print axioms cubeComm_matrix
#print axioms cubeComm_trace
#print axioms cubeConn_plaqEnergy_01
#print axioms cubeConn_wilsonAction
#print axioms cubeConn_not_flat'

end CubeToSU3.Lattice
