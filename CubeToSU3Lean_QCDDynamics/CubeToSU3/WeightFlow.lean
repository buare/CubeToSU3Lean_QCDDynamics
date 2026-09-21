import CubeToSU3.Core

/-!
# WeightFlow：權圖、根系與樸素 ODE 甲 `dv/dt = D v`

建在 `CubeToSU3.Core` 之上，直接使用 Core 的 `Vec3`、`Mat3`、`D`、`I3`、
`zeroSum` 與八個座標矩陣 `E01 … E21`。無 Mathlib；證明只用 `decide`、
`simp`、`omega`。投影權一律乘以 3，全在 ℤ³。

## 主要結果

* `D_eq_P_sub_P2`        : Core 的 D 就是 P − P²，P 為 (x,y,z) ↦ (y,z,x)
* `D_root_expansion`     : D = (E01 − E10) + (E12 − E21) + (E20 − E02)
* `D_e0/e1/e2`           : D eᵢ = e_{i+2} − e_{i+1}（基本權 ↦ 根）
* `D_weight_is_root_*`   : 六個非軸卦的權經 D 後全是 3 × 根
* `D_norm_ratio`         : |D w|² = 3|w|²
* `plane_P_from_D`       : 零和平面上 2P = −I + D（流在 120° 等於 P）
* `P_comm_D`             : P D = D P（Weyl ℤ₃ 在流裡）
* `swap_anticomm_D`      : T D = −D T，三個對換皆然（反射不在流裡）
* `R_sq_eq_P`, `R_cube_neg` : R = −P²，R² = P，R³ = −I
* `petrie_*`             : 震→離→艮→巽→坎→兌→震，每步一爻、層次交替、
                           兩步為 P、三步為錯卦
* `comp_weight`          : 錯卦 ⇒ 權取負（電荷共軛）
-/

namespace CubeToSU3
namespace WeightFlow

/-! ## 1. 向量小工具（Core 只有 `Vec3.scale`） -/

def vadd (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def vsub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def vneg (v : Vec3) : Vec3 := ⟨-v.x, -v.y, -v.z⟩
def norm2 (v : Vec3) : Int := v.x * v.x + v.y * v.y + v.z * v.z
def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

def e0 : Vec3 := ⟨1, 0, 0⟩
def e1 : Vec3 := ⟨0, 1, 0⟩
def e2 : Vec3 := ⟨0, 0, 1⟩
/-- 主對角線 n = (1,1,1)。 -/
def n  : Vec3 := ⟨1, 1, 1⟩

/-! ## 2. 循環位移 P、60° 旋轉 R、三個對換 -/

/-- 循環位移 P：(x,y,z) ↦ (y,z,x)。 -/
def P : Mat3 :=
  ⟨0, 1, 0,
   0, 0, 1,
   1, 0, 0⟩

/-- 六邊形的 60° 旋轉 R = −P²。 -/
def R : Mat3 := Mat3.neg (Mat3.mul P P)

/-- 對換兩個爻位（Weyl 群中的反射）。 -/
def T01 : Mat3 := ⟨0, 1, 0,  1, 0, 0,  0, 0, 1⟩
def T12 : Mat3 := ⟨1, 0, 0,  0, 0, 1,  0, 1, 0⟩
def T02 : Mat3 := ⟨0, 0, 1,  0, 1, 0,  1, 0, 0⟩

/-! ## 3. Core 的 D 與 P、根的關係（矩陣等式） -/

/-- Core 的 D 正是循環差分 P − P²。 -/
theorem D_eq_P_sub_P2 : D = Mat3.sub P (Mat3.mul P P) := by decide

theorem P_cube : Mat3.mul P (Mat3.mul P P) = I3 := by decide

/-- D 是三對反向根路徑之差的和：D 本身就活在根空間裡，沒有 Cartan 分量。 -/
theorem D_root_expansion :
    D = Mat3.sum [Mat3.sub E01 E10, Mat3.sub E12 E21, Mat3.sub E20 E02] := by
  decide

/-- 與講義一致：D v = v × n。 -/
theorem D_eq_cross (v : Vec3) : Mat3.mulVec D v = cross v n := by
  cases v with
  | mk x y z =>
    simp only [Mat3.mulVec, D, cross, n, Vec3.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem D_kills_n : Mat3.mulVec D n = ⟨0, 0, 0⟩ := by decide

/-! ## 4. D 把基本權送到根 -/

theorem D_e0 : Mat3.mulVec D e0 = vsub e2 e1 := by decide
theorem D_e1 : Mat3.mulVec D e1 = vsub e0 e2 := by decide
theorem D_e2 : Mat3.mulVec D e2 = vsub e1 e0 := by decide

/-! ## 5. 流的取樣：120° = P，反射到不了 -/

/-- 零和平面上 2P = −I + D。P 在平面上的特徵值 ω = (−1 + i√3)/2，
D 的特徵值 i√3，故這是「e^{Dt} 在 √3 t = 2π/3 時等於 P」的無 √3 整數版本。 -/
theorem plane_P_from_D (v : Vec3) (h : zeroSum v) :
    Vec3.scale 2 (Mat3.mulVec P v) = vadd (vneg v) (Mat3.mulVec D v) := by
  cases v with
  | mk x y z =>
    simp only [zeroSum] at h
    simp only [Vec3.scale, Mat3.mulVec, P, D, vadd, vneg, Vec3.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Weyl 群的循環部分與 D 交換：它活在流裡。 -/
theorem P_comm_D : Mat3.mul P D = Mat3.mul D P := by decide

/-- 三個對換都與 D 反交換。任何 e^{Dt} 都與 D 交換，所以反射不在流上。 -/
theorem swap_anticomm_D :
    Mat3.mul T01 D = Mat3.neg (Mat3.mul D T01) ∧
    Mat3.mul T12 D = Mat3.neg (Mat3.mul D T12) ∧
    Mat3.mul T02 D = Mat3.neg (Mat3.mul D T02) := by
  decide

/-- 反交換而非交換（因為 D ≠ 0）。 -/
theorem swap_not_comm_D : Mat3.mul T01 D ≠ Mat3.mul D T01 := by decide

/-! ## 6. 60° 步 R -/

theorem R_sq_eq_P : Mat3.mul R R = P := by decide

/-- 三個 60° 步 = −I：在權圖上就是錯卦（電荷共軛）。 -/
theorem R_cube_neg : Mat3.mul R (Mat3.mul R R) = Mat3.neg I3 := by decide

theorem R_comm_D : Mat3.mul R D = Mat3.mul D R := by decide

/-! ## 7. 八卦、陽爻數與權 -/

/-- 三爻：a = 初爻、b = 二爻、c = 三爻；true = 陽。 -/
structure Gua where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

def kun  : Gua := ⟨false, false, false⟩  -- 坤 ☷
def zhen : Gua := ⟨true,  false, false⟩  -- 震 ☳
def kan  : Gua := ⟨false, true,  false⟩  -- 坎 ☵
def gen  : Gua := ⟨false, false, true ⟩  -- 艮 ☶
def xun  : Gua := ⟨false, true,  true ⟩  -- 巽 ☴
def li   : Gua := ⟨true,  false, true ⟩  -- 離 ☲
def dui  : Gua := ⟨true,  true,  false⟩  -- 兌 ☱
def qian : Gua := ⟨true,  true,  true ⟩  -- 乾 ☰

def bit (t : Bool) : Int := if t then 1 else 0

def toV (g : Gua) : Vec3 := ⟨bit g.a, bit g.b, bit g.c⟩

/-- 陽爻數 = Λᵏℂ³ 的 k。 -/
def yang (g : Gua) : Int := bit g.a + bit g.b + bit g.c

/-- 投影權（乘 3）：w(g) = 3g − (陽爻數)·n。 -/
def w (g : Gua) : Vec3 := vsub (Vec3.scale 3 (toV g)) (Vec3.scale (yang g) n)

/-- 錯卦：三爻全翻。 -/
def comp (g : Gua) : Gua := ⟨!g.a, !g.b, !g.c⟩

def hamming (g h : Gua) : Nat :=
  (if g.a = h.a then 0 else 1) + (if g.b = h.b then 0 else 1)
    + (if g.c = h.c then 0 else 1)

/-- 每個權都落在 Core 的零和平面上。 -/
theorem w_zero_sum (g : Gua) : zeroSum (w g) := by
  unfold zeroSum
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

theorem w_axis : w qian = ⟨0, 0, 0⟩ ∧ w kun = ⟨0, 0, 0⟩ := by decide

/-- 錯卦 ⇒ 權取負：3 ↔ 3̄ 的電荷共軛。 -/
theorem comp_weight (g : Gua) : w (comp g) = vneg (w g) := by
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- 一陽卦的權就是 3eᵢ − n。 -/
theorem w_one_yang :
    w zhen = vsub (Vec3.scale 3 e0) n ∧
    w kan  = vsub (Vec3.scale 3 e1) n ∧
    w gen  = vsub (Vec3.scale 3 e2) n := by
  decide

/-! ## 8. 六個非軸卦的權經 D 全部變成（3 倍的）根 -/

theorem D_weight_is_root_zhen : Mat3.mulVec D (w zhen) = Vec3.scale 3 (vsub e2 e1) := by decide
theorem D_weight_is_root_kan  : Mat3.mulVec D (w kan)  = Vec3.scale 3 (vsub e0 e2) := by decide
theorem D_weight_is_root_gen  : Mat3.mulVec D (w gen)  = Vec3.scale 3 (vsub e1 e0) := by decide
theorem D_weight_is_root_xun  : Mat3.mulVec D (w xun)  = Vec3.scale 3 (vsub e1 e2) := by decide
theorem D_weight_is_root_li   : Mat3.mulVec D (w li)   = Vec3.scale 3 (vsub e2 e0) := by decide
theorem D_weight_is_root_dui  : Mat3.mulVec D (w dui)  = Vec3.scale 3 (vsub e0 e1) := by decide

/-- |D w|² = 3|w|²：根六邊形是權六邊形放大 √3 倍。 -/
theorem D_norm_ratio (g : Gua) : norm2 (Mat3.mulVec D (w g)) = 3 * norm2 (w g) := by
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-! ## 9. Petrie 六邊形：震→離→艮→巽→坎→兌→震 -/

/-- 立方體赤道 6-循環（乾坤不動）。 -/
def next (g : Gua) : Gua :=
  if g = zhen then li
  else if g = li then gen
  else if g = gen then xun
  else if g = xun then kan
  else if g = kan then dui
  else if g = dui then zhen
  else g

def nonAxial (g : Gua) : Prop := g ≠ qian ∧ g ≠ kun

instance (g : Gua) : Decidable (nonAxial g) := by
  unfold nonAxial; exact inferInstance

/-- 60° 旋轉 R 在權上實現 next。 -/
theorem petrie_is_R (g : Gua) (h : nonAxial g) :
    w (next g) = Mat3.mulVec R (w g) := by
  revert h
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- 每一步恰改一爻（立方體的一條棱，動爻）。 -/
theorem petrie_one_line (g : Gua) (h : nonAxial g) : hamming g (next g) = 1 := by
  revert h
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- 陽爻數在 1 與 2 之間交替：3 ↔ 3̄。 -/
theorem petrie_alternates (g : Gua) (h : nonAxial g) :
    yang g + yang (next g) = 3 := by
  revert h
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- 兩步留在同一層（爻位遷移），且在權上等於 P。 -/
theorem petrie_two_is_P (g : Gua) (h : nonAxial g) :
    w (next (next g)) = Mat3.mulVec P (w g) ∧ yang (next (next g)) = yang g := by
  revert h
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

/-- 三步即錯卦。 -/
theorem petrie_three_is_comp (g : Gua) (h : nonAxial g) :
    next (next (next g)) = comp g := by
  revert h
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

theorem petrie_period_six (g : Gua) :
    next (next (next (next (next (next g))))) = g := by
  cases g with
  | mk a b c => cases a <;> cases b <;> cases c <;> decide

end WeightFlow
end CubeToSU3
