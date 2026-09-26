import CubeToSU3.RootMatch

/-!
# 乾坤軸的穩定子：哪些立方體對稱真正穿過 `genOf` 這座橋

`Weyl.lean` 證明了 `Aut(Q₃)`（48 階）在 su(3) 上給出 24 個不同的自同構：
帶號置換矩陣的共軛。那個作用沒有看立方體的頂點往哪裡走——例如
`signAct` 把每個 `E_ij` 只乘上 `±1`，固定每個根空間，但對應的立方體變爻
卻會移動全部六個非軸頂點。所以那 24 個是「su(3) 的自同構」，
還不是「與立方體→根的標記相容的對稱」。

本檔問的是後者。`RootMatch.lean` 把頂點 `i` 標成根空間 `genOf i`
（乾、坤標成 0）。立方體對稱 `g` 稱為**與標記等變**，若存在 su(3) 的自同構
`φ`，使得對每個頂點 `i`，`φ` 把根空間 `genOf i` 送到根空間 `genOf (g i)`：

  `φ (genOf i) = ± genOf (g i)`。

候選的 `φ` 取 12 個：置換矩陣的共軛 `X ↦ P X Pᵀ`（6 個），以及它們再合成
Chevalley 對合 `θ X = -Xᵀ`（外自同構，即電荷共軛 `3 ↔ 3̄`）。

## 結果

* `equivariant_iff_fixes_axis`：`g` 與標記等變 ⟺ `g` 保持 {乾, 坤}。
* `fixes_axis_iff_flip`：保持乾坤軸 ⟺ 爻位翻轉只能是「不翻」或「全翻（錯卦）」。
* `equivariant_count`：48 個立方體對稱中恰有 12 個等變。
* `nontrivial_flip_hits_axis`：其他六種變爻，都會把某個非軸頂點（一個根）
  送到乾或坤（零）上，因此不可能等變。
* `cuo_is_charge_conjugation`：錯卦等變，但**只能**由 θ 實現；
  任何置換共軛（包括恆等映射）都不行。對照 `Weyl.lean` 的
  `signAct_flip_all_trivial`：在那個作用下錯卦是平凡的，在標記下它必須是
  電荷共軛。
* `theta_parity`：實現 `g` 的自同構帶 θ，若且唯若
  （爻位置換為奇置換）XOR（`g` 含錯卦）。這就是 `D` 只在差一個正負號下
  對奇置換等變的那個符號。

全部是有限檢查，以 `decide` 證明；不用 Mathlib，不引入新公理。
-/

namespace CubeToSU3.Stab

open CubeToSU3 CubeToSU3.Root

/-- 不用 Mathlib 時，核心 Lean 沒有 `∃ i : Fin n` 的可判定實例；由
    `Nat.decidableExistsLT'` 轉過來。 -/
instance decExistsFin {n : Nat} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ i, P i) :=
  decidable_of_iff (∃ m, ∃ h : m < n, P ⟨m, h⟩)
    ⟨fun ⟨m, h, hp⟩ => ⟨⟨m, h⟩, hp⟩, fun ⟨⟨m, h⟩, hp⟩ => ⟨m, h, hp⟩⟩

instance decExistsBool (P : Bool → Prop) [DecidablePred P] : Decidable (∃ b, P b) :=
  decidable_of_iff (P false ∨ P true)
    ⟨fun h => h.elim (⟨_, ·⟩) (⟨_, ·⟩),
     fun ⟨b, hb⟩ => by cases b <;> simp_all⟩

/-! ## 1. 立方體對稱：爻位置換 × 爻位翻轉 -/

/-- 六個爻位置換，以 `Fin 3 → Fin 3` 表示。第 `k` 爻的新值取自第 `perm p k` 爻。 -/
def perm : Fin 6 → Fin 3 → Fin 3
  | 0 => fun k => k                                    -- 恆等
  | 1 => fun k => match k with | 0 => 0 | 1 => 2 | 2 => 1  -- 換二三爻
  | 2 => fun k => match k with | 0 => 1 | 1 => 0 | 2 => 2  -- 換一二爻
  | 3 => fun k => match k with | 0 => 1 | 1 => 2 | 2 => 0  -- 輪換
  | 4 => fun k => match k with | 0 => 2 | 1 => 0 | 2 => 1  -- 輪換
  | 5 => fun k => match k with | 0 => 2 | 1 => 1 | 2 => 0  -- 換一三爻

/-- 奇置換（三個對換）。 -/
def odd : Fin 6 → Bool
  | 1 | 2 | 5 => true
  | _ => false

/-- 頂點 `i` 的第 `k` 個位元（與 `vtx01` 同一慣例）。 -/
def bit (i : Fin 8) (k : Fin 3) : Nat := (i.val / 2 ^ k.val) % 2

/-- 由三個位元組回頂點。 -/
def ofBits (b0 b1 b2 : Nat) : Fin 8 := Fin.ofNat' 8 (b0 % 2 + 2 * (b1 % 2) + 4 * (b2 % 2))

/-- 立方體對稱 `(p, f)` 作用在頂點上：先置換爻位，再與遮罩 `f` 做 XOR（變爻）。 -/
def act (p : Fin 6) (f : Fin 8) (i : Fin 8) : Fin 8 :=
  let w := fun k : Fin 3 => (bit i (perm p k) + bit f k) % 2
  ofBits (w 0) (w 1) (w 2)

/-- 保持乾坤軸（可以交換乾坤）。 -/
def fixesAxis (p : Fin 6) (f : Fin 8) : Prop :=
  (act p f 0 = 0 ∧ act p f 7 = 7) ∨ (act p f 0 = 7 ∧ act p f 7 = 0)

instance (p : Fin 6) (f : Fin 8) : Decidable (fixesAxis p f) := by
  unfold fixesAxis; infer_instance

/-- 健全性：`act` 確實是 48 個不同的頂點置換中的一員——每一個都是雙射。 -/
theorem act_injective : ∀ p : Fin 6, ∀ f : Fin 8, ∀ i j : Fin 8,
    act p f i = act p f j → i = j := by decide

/-- 健全性：`act` 保持立方體的邊（漢明距離 1 的頂點對）。 -/
def hamming1 (i j : Fin 8) : Bool :=
  (bit i 0 + bit j 0) % 2 + (bit i 1 + bit j 1) % 2 + (bit i 2 + bit j 2) % 2 == 1

theorem act_preserves_edges : ∀ p : Fin 6, ∀ f : Fin 8, ∀ i j : Fin 8,
    hamming1 i j = hamming1 (act p f i) (act p f j) := by decide

/-! ## 2. su(3) 一側的候選自同構 -/

def entry (X : Mat3) : Fin 3 → Fin 3 → Int
  | 0, 0 => X.a00 | 0, 1 => X.a01 | 0, 2 => X.a02
  | 1, 0 => X.a10 | 1, 1 => X.a11 | 1, 2 => X.a12
  | 2, 0 => X.a20 | 2, 1 => X.a21 | 2, 2 => X.a22

def ofEntry (e : Fin 3 → Fin 3 → Int) : Mat3 :=
  ⟨e 0 0, e 0 1, e 0 2, e 1 0, e 1 1, e 1 2, e 2 0, e 2 1, e 2 2⟩

/-- 置換矩陣的共軛，寫成重排矩陣元。 -/
def conjPerm (q : Fin 6) (X : Mat3) : Mat3 :=
  ofEntry fun a b => entry X (perm q a) (perm q b)

/-- Chevalley 對合 `θ X = -Xᵀ`：su(3) 的外自同構，把 `3` 換成 `3̄`。 -/
def theta (X : Mat3) : Mat3 :=
  ofEntry fun a b => - entry X b a

/-- 候選自同構：置換共軛，視 `t` 決定是否先做 θ。 -/
def phi (q : Fin 6) (t : Bool) (X : Mat3) : Mat3 :=
  conjPerm q (if t then theta X else X)

/-- θ 保持李括號（在全部生成元上檢查）。 -/
theorem theta_bracket : ∀ i j : Fin 8,
    theta (Mat3.commutator (genOf i) (genOf j))
      = Mat3.commutator (theta (genOf i)) (theta (genOf j)) := by decide

/-- 置換共軛保持李括號（在全部生成元上檢查）。 -/
theorem conjPerm_bracket : ∀ q : Fin 6, ∀ i j : Fin 8,
    conjPerm q (Mat3.commutator (genOf i) (genOf j))
      = Mat3.commutator (conjPerm q (genOf i)) (conjPerm q (genOf j)) := by decide

/-! ## 3. 等變性 -/

/-- `φ = phi q t` 把每個根空間 `genOf i` 送到 `genOf (g i)`（差一個正負號）。 -/
def Works (p : Fin 6) (f : Fin 8) (q : Fin 6) (t : Bool) : Prop :=
  ∀ i : Fin 8, phi q t (genOf i) = genOf (act p f i) ∨
               phi q t (genOf i) = Mat3.neg (genOf (act p f i))

instance (p : Fin 6) (f : Fin 8) (q : Fin 6) (t : Bool) : Decidable (Works p f q t) := by
  unfold Works; infer_instance

/-- 立方體對稱 `(p, f)` 與 `genOf` 標記等變。 -/
def Equivariant (p : Fin 6) (f : Fin 8) : Prop :=
  ∃ q : Fin 6, ∃ t : Bool, Works p f q t

instance (p : Fin 6) (f : Fin 8) : Decidable (Equivariant p f) := by
  unfold Equivariant; infer_instance

/-- **主定理。** 與標記等變 ⟺ 保持乾坤軸。 -/
theorem equivariant_iff_fixes_axis : ∀ p : Fin 6, ∀ f : Fin 8,
    Equivariant p f ↔ fixesAxis p f := by decide

/-- 保持乾坤軸 ⟺ 變爻遮罩只能是「不變」或「錯卦」。爻位置換不受限。 -/
theorem fixes_axis_iff_flip : ∀ p : Fin 6, ∀ f : Fin 8,
    fixesAxis p f ↔ (f = 0 ∨ f = 7) := by decide

def allP : List (Fin 6) := [0, 1, 2, 3, 4, 5]
def allF : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- 48 個立方體對稱中恰有 12 個等變。 -/
theorem equivariant_count :
    (allP.flatMap fun p => allF.filter fun f => decide (Equivariant p f)).length = 12 := by
  decide

/-- 其餘六種變爻都把某個根送到乾或坤上（零），所以不可能等變。 -/
theorem nontrivial_flip_hits_axis : ∀ f : Fin 8, f ≠ 0 → f ≠ 7 →
    ∃ i : Fin 8, i ≠ 0 ∧ i ≠ 7 ∧ (act 0 f i = 0 ∨ act 0 f i = 7) := by decide

/-- **錯卦 = 電荷共軛。** 錯卦由 θ 實現，而且沒有任何置換共軛（θ 之外）能實現它。
    特別地，恆等映射——也就是 `Weyl.lean` 中 `signAct (-1) (-1) (-1)` 的作用——
    與標記不相容。 -/
theorem cuo_is_charge_conjugation :
    Works 0 7 0 true ∧ ∀ q : Fin 6, ¬ Works 0 7 q false := by decide

/-- 實現等變對稱的自同構是唯一的，而且帶 θ 若且唯若
    （爻位置換為奇）XOR（含錯卦）。 -/
theorem theta_parity : ∀ p : Fin 6, ∀ f : Fin 8, ∀ q : Fin 6, ∀ t : Bool,
    Works p f q t → t = (odd p != (f == 7)) := by decide

theorem realiser_unique : ∀ p : Fin 6, ∀ f : Fin 8, ∀ q q' : Fin 6, ∀ t t' : Bool,
    Works p f q t → Works p f q' t' → q = q' ∧ t = t' := by decide

end CubeToSU3.Stab
