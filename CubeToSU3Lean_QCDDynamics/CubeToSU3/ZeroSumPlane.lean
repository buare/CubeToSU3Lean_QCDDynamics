import CubeToSU3.QianKunAxis

/-!
# 乾坤平面的三重身分：三個座標、二維實平面、一維複直線

沿乾坤軸 `(1,1,1)` 正對著看立方體，八卦被投影到平面
`Π = { v : x + y + z = 0 }`。這個平面同時有三種「維度」：

1. **三個座標**：Π 的點仍用三個分量寫出，三個爻位完全平等，
   爻位的六個置換（S₃）都把 Π 送回 Π。
2. **二維實平面**：`ℤ³` 在乘 3 之後拆成「乾坤軸 ⊕ Π」，而且拆法唯一；
   Π 由兩個向量張成；S₃ 在 Π 上**忠實**作用。
3. **一維複直線**：D 在 Π 上可逆，`D² = -3`、`D⁴ = 9`，所以 `D/√3` 是
   一個複結構（「乘 i」＝「繞乾坤軸轉 90°」）。偶置換與 D 交換（全純），
   奇置換與 D 反交換（反全純，即複共軛）——這正是
   `QianKunStabilizer.theta_parity` 裡奇置換必須配上 θ 的原因。

用表示論的話說：S₃ 在 ℝ³ 上的置換表示＝平凡表示（乾坤軸）⊕ 二維標準表示（Π），
而 D 把標準表示變成一條複直線。

座標全部在 `Int`；投影沿用 `QianKunAxis.proj`（乘 3 以保持整數）。
全部證明只用 `decide`、`simp`、`omega`；不用 Mathlib，不引入新公理。
-/

namespace CubeToSU3.Plane

open CubeToSU3 CubeToSU3.Axis

/-! ## 1. 平面與軸 -/

/-- 軸上的點 `c·(1,1,1)`。 -/
def onAxis (c : Int) : Vec3 := ⟨c, c, c⟩

/-- 在平面上 ⟺ 與乾坤軸正交。 -/
theorem plane_iff_orthogonal (v : Vec3) : zeroSum v ↔ dot v axisD = 0 := by
  cases v with
  | mk x y z => simp [zeroSum, dot, axisD]

/-- 投影一定落在平面上（對任意整數向量，不只是八個頂點）。 -/
theorem proj_in_plane (v : Vec3) : zeroSum (proj v) := by
  cases v with
  | mk x y z => simp [zeroSum, proj, dot, axisD]; omega

/-- 軸上的點被壓成原點。 -/
theorem proj_kills_axis (c : Int) : proj (onAxis c) = ⟨0, 0, 0⟩ := by
  simp [proj, onAxis, dot, axisD, Vec3.mk.injEq]; omega

/-- 平面上的點只被放大 3 倍，方向不變。 -/
theorem proj_on_plane (v : Vec3) (h : zeroSum v) : proj v = Vec3.scale 3 v := by
  cases v with
  | mk x y z =>
    simp [zeroSum] at h
    simp [proj, dot, axisD, Vec3.scale, Vec3.mk.injEq]; omega

/-- **分解。** `3v = (沿軸的部分) + (平面上的部分)`；沿軸部分是三爻之和。 -/
theorem axis_plus_plane (v : Vec3) :
    Vec3.scale 3 v =
      ⟨(onAxis (dot v axisD)).x + (proj v).x,
       (onAxis (dot v axisD)).y + (proj v).y,
       (onAxis (dot v axisD)).z + (proj v).z⟩ := by
  cases v with
  | mk x y z => simp [Vec3.scale, onAxis, proj, dot, axisD, Vec3.mk.injEq]; omega

/-- **分解唯一**：軸與平面只交於原點，所以這是直和。 -/
theorem decomposition_unique (a a' : Int) (w w' : Vec3)
    (hw : zeroSum w) (hw' : zeroSum w')
    (h : (⟨a + w.x, a + w.y, a + w.z⟩ : Vec3) = ⟨a' + w'.x, a' + w'.y, a' + w'.z⟩) :
    a = a' ∧ w = w' := by
  cases w with
  | mk x y z =>
    cases w' with
    | mk x' y' z' =>
      simp [zeroSum] at hw hw'
      simp [Vec3.mk.injEq] at h ⊢
      omega

/-! ## 2. 二維：兩個向量張成平面 -/

def e1 : Vec3 := ⟨1, -1, 0⟩
def e2 : Vec3 := ⟨0, 1, -1⟩

/-- 平面上的點由前兩個座標決定：`v = x·e1 + (x+y)·e2`。三個座標、兩個自由度。 -/
theorem plane_spanned (v : Vec3) (h : zeroSum v) :
    v = ⟨v.x * e1.x + (v.x + v.y) * e2.x,
         v.x * e1.y + (v.x + v.y) * e2.y,
         v.x * e1.z + (v.x + v.y) * e2.z⟩ := by
  cases v with
  | mk x y z =>
    simp [zeroSum] at h
    simp [e1, e2, Vec3.mk.injEq]; omega

/-- `e1`、`e2` 線性獨立：`a·e1 + b·e2 = 0` 只有零解。 -/
theorem e1_e2_independent (a b : Int)
    (h : (⟨a * e1.x + b * e2.x, a * e1.y + b * e2.y, a * e1.z + b * e2.z⟩ : Vec3)
          = ⟨0, 0, 0⟩) : a = 0 ∧ b = 0 := by
  simp [e1, e2, Vec3.mk.injEq] at h; omega

/-! ## 3. 三個座標：S₃ 保持平面並忠實作用 -/

/-- 六個爻位置換，作用在座標上。 -/
def permVec : Fin 6 → Vec3 → Vec3
  | 0, v => v
  | 1, v => ⟨v.x, v.z, v.y⟩
  | 2, v => ⟨v.y, v.x, v.z⟩
  | 3, v => ⟨v.y, v.z, v.x⟩
  | 4, v => ⟨v.z, v.x, v.y⟩
  | 5, v => ⟨v.z, v.y, v.x⟩

/-- 奇置換（三個對換）。 -/
def oddPerm : Fin 6 → Bool
  | 1 | 2 | 5 => true
  | _ => false

theorem permVec_preserves_plane (p : Fin 6) (v : Vec3) (h : zeroSum v) :
    zeroSum (permVec p v) := by
  cases v with
  | mk x y z =>
    simp [zeroSum] at h
    match p with
    | 0 | 1 | 2 | 3 | 4 | 5 => simp [permVec, zeroSum]; omega

theorem permVec_fixes_axis (p : Fin 6) (c : Int) : permVec p (onAxis c) = onAxis c := by
  match p with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl

/-- 平面上的測試向量（零和）。 -/
def w0 : Vec3 := ⟨1, 0, -1⟩

theorem w0_in_plane : zeroSum w0 := by simp [zeroSum, w0]

/-- **忠實性。** 六個置換在平面上仍是六個不同的變換：
    三維的對稱完整地活在二維平面裡。 -/
theorem permVec_faithful_on_plane : ∀ p q : Fin 6, permVec p w0 = permVec q w0 → p = q := by
  decide

/-! ## 4. 一維複直線：D 是複結構 -/

/-- D 的核恰好是乾坤軸。 -/
theorem D_kernel (v : Vec3) :
    Mat3.mulVec D v = ⟨0, 0, 0⟩ ↔ v.x = v.y ∧ v.y = v.z := by
  cases v with
  | mk x y z => simp [Mat3.mulVec, D, Vec3.mk.injEq]; omega

/-- 所以 D 在平面上是單射：平面上沒有被 D 壓掉的方向。 -/
theorem D_injective_on_plane (v : Vec3) (h : zeroSum v)
    (h0 : Mat3.mulVec D v = ⟨0, 0, 0⟩) : v = ⟨0, 0, 0⟩ := by
  rw [D_kernel] at h0
  cases v with
  | mk x y z =>
    simp [zeroSum] at h h0
    simp [Vec3.mk.injEq]; omega

/-- 轉四次 90°＝轉一整圈（放大 9 倍）。 -/
theorem D_fourth_on_plane (v : Vec3) (h : zeroSum v) :
    Mat3.mulVec D (Mat3.mulVec D (Mat3.mulVec D (Mat3.mulVec D v))) = Vec3.scale 9 v := by
  cases v with
  | mk x y z =>
    simp [zeroSum] at h
    simp [Mat3.mulVec, D, Vec3.scale, Vec3.mk.injEq]; omega

def negVec (v : Vec3) : Vec3 := ⟨-v.x, -v.y, -v.z⟩

/-- **偶置換全純、奇置換反全純。** 偶置換與 D 交換（保持「乘 i」），
    奇置換與 D 反交換（把 i 換成 −i，即複共軛）。 -/
theorem D_perm_parity (p : Fin 6) (v : Vec3) :
    Mat3.mulVec D (permVec p v) =
      (if oddPerm p then negVec (permVec p (Mat3.mulVec D v))
       else permVec p (Mat3.mulVec D v)) := by
  cases v with
  | mk x y z =>
    match p with
    | 0 | 1 | 2 | 3 | 4 | 5 =>
      simp [Mat3.mulVec, D, permVec, oddPerm, negVec, Vec3.mk.injEq] <;> omega

end CubeToSU3.Plane
