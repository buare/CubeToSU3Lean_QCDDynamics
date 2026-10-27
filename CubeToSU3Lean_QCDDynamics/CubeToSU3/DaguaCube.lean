/-!
# 玄空大卦與羅盤圓圖：有限幾何的定理（本對話的形式化）

只用 Lean 核心，不需要 Mathlib，也不依賴 `CubeToSU3` 其他檔案，可以單獨編譯。
全部證明用 `decide`（或由 `decide` 得到的引理做幾行推理）。

## 編號（沿用 `QianKunAxis` / `WuxingBridge`）
一個三爻卦是 `Fin 8`：bit2 = 初爻（下）、bit1 = 二爻、bit0 = 三爻（上）。
  坤 0  艮 1  坎 2  巽 3  震 4  離 5  兌 6  乾 7
六十四卦寫成 (上卦, 下卦)。六爻依序：初 二 三 = 下卦 bit2 bit1 bit0；四 五 上 = 上卦 bit2 bit1 bit0。

## 內容
1. 卦數 = N(上卦)、卦運 = N(上卦 XOR 下卦)，逐卦對公開分運表
2. 換座標 T(上, 下) = (上, 上⊕下) 是對合；同運 = 對角子群的陪集
3. 洛書編號 N：閉式、合十／合生成／合五 = 克萊因四元群、上元下元 = 奇偶
4. 球殼 8/24/24/8、父母、變一爻 = 圖同態、同運兩卦相差偶數爻
5. 疊卦立方體：λ = 2 的長方盒、λ = 1 退化成 27 點
6. 羅盤先天圓圖：對面是錯卦、分段、相鄰差爻的分佈
7. 第二版粒子字典：六爻奇偶 = 弱1、質量配對必跨元、兩張座標圖互相橫截
8. 卦數的選法：和對角子群互補的子空間至少 512 個（上卦、下卦都在其中）
9. XOR 與共軛：只有 XOR 乾把 3 與 3̄ 整層互換；群論共軛要靠爻位交換；綜卦不是 XOR

對應的筆記：notes/LUOPAN_DAGUA.md（claude.ai 專案「白話群論」裡是 claude/LUOPAN_DAGUA.md）。
已用 Lean 4.16.0（本 repo 的版本）與 4.19.0 編譯通過。本檔只處理編號與排列的結構，不涉及吉凶。
-/

set_option maxRecDepth 20000

namespace CubeToSU3.Dagua

/-! ## 0. 基本運算 -/

/-- 自然數取 mod 8 變成三爻卦 -/
def f8 (n : Nat) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

/-- 逐爻比較：相同記陰、不同記陽（XOR） -/
def xo (a b : Fin 8) : Fin 8 := f8 (a.val ^^^ b.val)

/-- 第 k 個位元（k = 0 三爻、1 二爻、2 初爻） -/
def bit (a : Fin 8) (k : Nat) : Nat := a.val / 2 ^ k % 2

/-- 陽爻數 -/
def yao (a : Fin 8) : Nat := bit a 0 + bit a 1 + bit a 2

/-- 兩卦差幾爻 -/
def ham (a b : Fin 8) : Nat := yao (xo a b)

/-- 先天卦配洛書數：坤1 艮6 坎7 巽2 震8 離3 兌4 乾9 -/
def N : Fin 8 → Nat
  | 0 => 1 | 1 => 6 | 2 => 7 | 3 => 2 | 4 => 8 | 5 => 3 | 6 => 4 | 7 => 9

/-- 卦數 -/
def shu (up _lo : Fin 8) : Nat := N up
/-- 卦運 -/
def yun (up lo : Fin 8) : Nat := N (xo up lo)

/-! ## 1. 兩條公式對公開分運表

資料：生活易經一起看〈論『玄空大卦』之基本功〉
https://siewwong.blogspot.com/2015/11/blog-post_18.html
每一項是 (運, 上卦, 下卦)。 -/

def pub : List (Nat × Fin 8 × Fin 8) := [
  -- 1 運：乾 坎 艮 震 巽 離 坤 兌
  (1, 7, 7), (1, 2, 2), (1, 1, 1), (1, 4, 4), (1, 3, 3), (1, 5, 5), (1, 0, 0), (1, 6, 6),
  -- 9 運：泰 否 恆 益 咸 損 未濟 既濟
  (9, 0, 7), (9, 7, 0), (9, 4, 3), (9, 3, 4), (9, 6, 1), (9, 1, 6), (9, 5, 2), (9, 2, 5),
  -- 2 運：無妄 大壯 升 觀 革 睽 蹇 蒙
  (2, 7, 4), (2, 4, 7), (2, 0, 3), (2, 3, 0), (2, 6, 5), (2, 5, 6), (2, 2, 1), (2, 1, 2),
  -- 8 運：困 節 賁 旅 復 豫 小畜 姤
  (8, 6, 2), (8, 2, 6), (8, 1, 5), (8, 5, 1), (8, 0, 4), (8, 4, 0), (8, 3, 7), (8, 7, 3),
  -- 3 運：明夷 頤 中孚 需 訟 大過 小過 晉
  (3, 0, 5), (3, 1, 4), (3, 3, 6), (3, 2, 7), (3, 7, 2), (3, 6, 3), (3, 4, 1), (3, 5, 0),
  -- 7 運：師 同人 歸妹 大有 比 漸 隨 蠱
  (7, 0, 2), (7, 7, 5), (7, 4, 6), (7, 5, 7), (7, 2, 0), (7, 3, 1), (7, 6, 4), (7, 1, 3),
  -- 4 運：屯 家人 大畜 鼎 解 遯 萃 臨
  (4, 2, 4), (4, 3, 5), (4, 1, 7), (4, 5, 3), (4, 4, 2), (4, 7, 1), (4, 6, 0), (4, 0, 6),
  -- 6 運：噬嗑 豐 夬 履 井 渙 剝 謙
  (6, 5, 4), (6, 4, 5), (6, 6, 7), (6, 7, 6), (6, 2, 3), (6, 3, 2), (6, 1, 0), (6, 0, 1)]

/-- 公開表有 64 項，涵蓋全部 64 卦（所以每卦恰好一次） -/
theorem pub_complete :
    pub.length = 64 ∧ ∀ u l : Fin 8, pub.any (fun p => p.2.1 == u && p.2.2 == l) = true := by
  decide

/-- 卦運 = N(上卦 XOR 下卦)：64 卦全部與公開表相符 -/
theorem pub_matches : pub.all (fun p => yun p.2.1 p.2.2 == p.1) = true := by decide

/-! ## 2. 換座標 T 與同運 -/

/-- (上, 下) ↦ (上, 上⊕下)：第一個分量給卦數、第二個給卦運 -/
def T (x : Fin 8 × Fin 8) : Fin 8 × Fin 8 := (x.1, xo x.1 x.2)

/-- T 是對合（自己的反函數），所以 64 卦 ↔ 卦數 × 卦運 是一一對應 -/
theorem T_involution : ∀ u l : Fin 8, T (T (u, l)) = (u, l) := by decide

/-- 給定上卦與「差卦」r，下卦唯一：每一運恰好 8 卦 -/
theorem fiber_param : ∀ r u l : Fin 8, xo u l = r ↔ l = xo u r := by decide

/-- 上下卦一起 XOR 同一個卦（同位一起變），卦運不變：同運 = 對角子群的陪集 -/
theorem diag_invariant : ∀ u l a : Fin 8, xo (xo u a) (xo l a) = xo u l := by decide

/-- 自己 XOR 自己是坤：八純卦都是一運 -/
theorem pure_is_yun1 : ∀ u : Fin 8, yun u u = 1 := by decide

/-! ## 3. 洛書編號 N -/

/-- 閉式：N = 1 + 2·初 + 二 + 5·(三爻奇偶) -/
theorem N_closed : ∀ r : Fin 8,
    N r = 1 + 2 * bit r 2 + bit r 1 + 5 * ((bit r 0 + bit r 1 + bit r 2) % 2) := by decide

/-- 合十：XOR 乾（取錯卦），N + N' = 10 -/
theorem he_shi : ∀ r : Fin 8, N r + N (xo r 7) = 10 := by decide

/-- 合生成（河圖 1-6、2-7、3-8、4-9）：XOR 艮（只翻三爻），差 5 -/
theorem he_shengcheng : ∀ r : Fin 8, N r + 5 = N (xo r 1) ∨ N (xo r 1) + 5 = N r := by decide

/-- 合五／合十五：XOR 兌（翻初、二爻），和為 5 或 15 -/
theorem he_wu : ∀ r : Fin 8, N r + N (xo r 6) = 5 ∨ N r + N (xo r 6) = 15 := by decide

/-- 三種「合」加上不動 = {坤, 艮, 兌, 乾} 是克萊因四元群：封閉、每個元素自己的反元素 -/
def Hmem (a : Fin 8) : Bool := a == 0 || a == 1 || a == 6 || a == 7

theorem he_klein :
    (∀ a b : Fin 8, Hmem a = true → Hmem b = true → Hmem (xo a b) = true) ∧
    (∀ a : Fin 8, xo a a = 0) ∧ xo 1 6 = 7 := by decide

/-- 上元（1～4）＝ 上下卦不同爻數為偶數 -/
theorem yuan_parity : ∀ r : Fin 8, N r < 5 ↔ yao r % 2 = 0 := by decide

/-- 同一件事用六爻說：上元 ＝ 六爻陽數為偶數 -/
theorem yuan_parity_hex : ∀ u l : Fin 8, yun u l < 5 ↔ (yao u + yao l) % 2 = 0 := by decide

/-- N 打破三條爻軸的平等：只翻一爻的三個差卦（艮、坎、震）號碼不同 -/
theorem N_not_symmetric : N 1 = 6 ∧ N 2 = 7 ∧ N 4 = 8 := by decide

/-! ## 4. 球殼、父母、變爻 -/

/-- 依「上下卦差幾爻」數卦 -/
def countShell (k : Nat) : Nat :=
  ((List.range 64).filter (fun h => ham (f8 (h / 8)) (f8 h) == k)).length

/-- 球殼 8、24、24、8 -/
theorem shells : (countShell 0, countShell 1, countShell 2, countShell 3) = (8, 24, 24, 8) := by
  decide

/-- 父母：差一爻的是六七八運（一為父母），差兩爻的是二三四運（九為父母） -/
theorem parents : ∀ r : Fin 8,
    (yao r = 0 ↔ N r = 1) ∧
    (yao r = 1 ↔ (N r = 6 ∨ N r = 7 ∨ N r = 8)) ∧
    (yao r = 2 ↔ (N r = 2 ∨ N r = 3 ∨ N r = 4)) ∧
    (yao r = 3 ↔ N r = 9) := by decide

/-- 變一爻（上卦或下卦的任一爻）：差卦恰好變一爻，必定換到相鄰的運。
    也就是 (上, 下) ↦ 上⊕下 把六爻超立方體的每一條邊送到三爻立方體的一條邊。 -/
theorem one_flip_adjacent : ∀ u l e : Fin 8, yao e = 1 →
    ham (xo u l) (xo (xo u e) l) = 1 ∧ ham (xo u l) (xo u (xo l e)) = 1 := by decide

/-- 同運兩卦（同位一起變 a）在六爻上相差 2·(a 的陽爻數) 爻：只能差 0、2、4、6 -/
theorem same_yun_even : ∀ u r a : Fin 8,
    ham u (xo u a) + ham (xo u r) (xo (xo u a) r) = 2 * yao a := by decide

/-! ## 5. 疊卦立方體（上下疊：上卦 = 大立方體 R，下卦 = 小立方體 r） -/

/-- 第 k 軸的座標，R = 2、r = 1（4×4×4 均勻格子） -/
def coord2 (u l : Fin 8) (k : Nat) : Int :=
  2 * (2 * (bit u k : Int) - 1) + (2 * (bit l k : Int) - 1)

/-- 長方盒：上下同爻的軸 |座標| = 3（外側），異爻的軸 = 1（內側） -/
theorem box_axes : ∀ u l : Fin 8, ∀ k : Fin 3,
    (coord2 u l k.val).natAbs = (if bit u k.val = bit l k.val then 3 else 1) := by decide

/-- 卦限（座標正負）由上卦決定 -/
theorem octant_is_upper : ∀ u l : Fin 8, ∀ k : Fin 3,
    (0 < coord2 u l k.val ↔ bit u k.val = 1) := by decide

/-- R = 2：64 卦落在 64 個不同的格點（每軸 4 個值，編號滿射到 0..63） -/
def code64 (u l : Fin 8) : Nat :=
  (2 * bit u 0 + bit l 0) + 4 * (2 * bit u 1 + bit l 1) + 16 * (2 * bit u 2 + bit l 2)

theorem lambda2_distinct :
    (List.range 64).all (fun q => (List.range 64).any (fun h => code64 (f8 (h / 8)) (f8 h) == q))
      = true := by decide

/-- R = r：每軸座標 (2u−1)+(2l−1) ∈ {−2, 0, 2}，編成 u+l ∈ {0,1,2}；64 卦落在 27 個點 -/
def code27 (u l : Fin 8) : Nat :=
  (bit u 0 + bit l 0) + 3 * (bit u 1 + bit l 1) + 9 * (bit u 2 + bit l 2)

theorem lambda1_27 :
    (List.range 64).all (fun h => code27 (f8 (h / 8)) (f8 h) < 27) = true ∧
    (List.range 27).all (fun q => (List.range 64).any (fun h => code27 (f8 (h / 8)) (f8 h) == q))
      = true := by decide

/-- R = r 時九運（上下卦互為錯卦）全部縮到中心 (0,0,0)，編號 1 + 3 + 9 = 13 -/
theorem yun9_center : ∀ u : Fin 8, code27 u (xo u 7) = 13 := by decide

/-! ## 6. 羅盤先天圓圖

從午起逆時針第 p 位（0 ≤ p < 64）：橫圖編號 63 − p（p < 32）或 p − 32（p ≥ 32）。
橫圖編號以初爻為最高位，所以 下卦 = 編號 / 8、上卦 = 編號 % 8。 -/

def circIdx (p : Nat) : Nat := if p < 32 then 63 - p else p - 32
def cUp (p : Nat) : Fin 8 := f8 (circIdx p % 8)
def cLo (p : Nat) : Fin 8 := f8 (circIdx p / 8)

/-- 第 0 位乾、第 32 位坤、最後一位姤（上乾下巽） -/
theorem circ_ends : (cUp 0, cLo 0) = (7, 7) ∧ (cUp 32, cLo 32) = (0, 0) ∧ (cUp 63, cLo 63) = (7, 3) := by
  decide

/-- 對面兩卦互為錯卦；所以卦運相同、卦數合十 -/
theorem circ_opposite : ∀ p : Fin 32,
    xo (cUp p.val) (cUp (p.val + 32)) = 7 ∧ xo (cLo p.val) (cLo (p.val + 32)) = 7 ∧
    yun (cUp p.val) (cLo p.val) = yun (cUp (p.val + 32)) (cLo (p.val + 32)) ∧
    shu (cUp p.val) (cLo p.val) + shu (cUp (p.val + 32)) (cLo (p.val + 32)) = 10 := by decide

/-- 每 8 位一段，下卦相同，依序 乾 兌 離 震 坤 艮 坎 巽（先天八卦方位） -/
def sect : List (Fin 8) := [7, 6, 5, 4, 0, 1, 2, 3]

theorem circ_sectors : ∀ p : Fin 64, cLo p.val = sect.getD (p.val / 8) 0 := by decide

/-- 每一段裡，八個卦運、八個卦數各出現一次 -/
def segCount (f : Fin 8 → Fin 8 → Nat) (s v : Nat) : Nat :=
  ((List.range 8).filter (fun i => f (cUp (8 * s + i)) (cLo (8 * s + i)) == v)).length

theorem circ_each_once :
    (List.range 8).all (fun s => [1, 2, 3, 4, 6, 7, 8, 9].all (fun v =>
      segCount yun s v == 1 && segCount shu s v == 1)) = true := by decide

/-- 相鄰兩卦差幾爻：1 爻 34 對、2 爻 16、3 爻 8、4 爻 4、5 爻 2（不是一筆畫） -/
def stepDist (p : Nat) : Nat :=
  ham (cUp p) (cUp ((p + 1) % 64)) + ham (cLo p) (cLo ((p + 1) % 64))

def stepCount (d : Nat) : Nat := ((List.range 64).filter (fun p => stepDist p == d)).length

theorem circ_steps :
    (stepCount 1, stepCount 2, stepCount 3, stepCount 4, stepCount 5) = (34, 16, 8, 4, 2) := by
  decide

/-! ## 7. 第二版粒子字典（RULES_V2.md）

交錯疊：內卦（色）= 初、三、五爻；外卦 = 二、四、上爻。
c = 色陽數，w2 = 外卦陽數奇偶，w1 = (c + w2) mod 2，3Q = 3·w1 − c。 -/

def chu (_u l : Fin 8) : Nat := bit l 2
def er  (_u l : Fin 8) : Nat := bit l 1
def san (_u l : Fin 8) : Nat := bit l 0
def si  (u _l : Fin 8) : Nat := bit u 2
def wu  (u _l : Fin 8) : Nat := bit u 1
def shang (u _l : Fin 8) : Nat := bit u 0

def colorC (u l : Fin 8) : Nat := chu u l + san u l + wu u l
def w2 (u l : Fin 8) : Nat := (er u l + si u l + shang u l) % 2
def w1 (u l : Fin 8) : Nat := (colorC u l + w2 u l) % 2
def charge3 (u l : Fin 8) : Int := 3 * (w1 u l : Int) - (colorC u l : Int)

/-- 六爻陽數奇偶 = 弱1 -/
theorem parity_is_w1 : ∀ u l : Fin 8, (yao u + yao l) % 2 = w1 u l := by decide

/-- 上元（陽數偶）電荷全 ≤ 0，下元（陽數奇）電荷全 ≥ 0 -/
theorem yuan_charge_sign : ∀ u l : Fin 8,
    (yun u l < 5 → charge3 u l ≤ 0) ∧ (5 < yun u l → 0 ≤ charge3 u l) := by decide

/-- 質量配對（內卦取錯卦：翻初、三、五爻）必定跨元 -/
theorem mass_pair_crosses : ∀ u l : Fin 8, w1 (xo u 2) (xo l 5) ≠ w1 u l := by decide

/-- 變一個外卦爻（二、四、上）：電荷變 ±1 -/
theorem outer_flip_charge : ∀ u l : Fin 8,
    (charge3 u (xo l 2) - charge3 u l = 3 ∨ charge3 u (xo l 2) - charge3 u l = -3) ∧
    (charge3 (xo u 4) l - charge3 u l = 3 ∨ charge3 (xo u 4) l - charge3 u l = -3) ∧
    (charge3 (xo u 1) l - charge3 u l = 3 ∨ charge3 (xo u 1) l - charge3 u l = -3) := by decide

/-- 變一個內卦爻（初、三、五）：電荷變 ±2/3 或 ±4/3 -/
def innerOk (d : Int) : Bool := d == 2 || d == -2 || d == 4 || d == -4

theorem inner_flip_charge : ∀ u l : Fin 8,
    innerOk (charge3 u (xo l 4) - charge3 u l) = true ∧
    innerOk (charge3 u (xo l 1) - charge3 u l) = true ∧
    innerOk (charge3 (xo u 2) l - charge3 u l) = true := by decide

/-- 兩張座標圖互相橫截：同一運（上 = 下⊕r）裡，交錯疊的內卦隨下卦一一對應 -/
def innerCode (u l : Fin 8) : Nat := 4 * chu u l + 2 * san u l + wu u l
def outerCode (u l : Fin 8) : Nat := 4 * er u l + 2 * si u l + shang u l

theorem transversal : ∀ r v v' : Fin 8,
    (innerCode (xo v r) v = innerCode (xo v' r) v' → v = v') ∧
    (outerCode (xo v r) v = outerCode (xo v' r) v' → v = v') := by decide

/-! ## 8. 卦數的選法：和對角子群互補的子空間

對角子群 Δ = {(a, a)}。任取線性映射 φ : F₂³ → F₂³（3×3 的 0/1 矩陣，共 512 個），
K_φ = {(x ⊕ φx, φx)} 是和 Δ 互補的子空間。φ = 0 是「上卦方向」，φ = 恆等 是「下卦方向」。
這裡證明這 512 個兩兩不同（下界）；「互補子空間恰好 512 個」是標準線性代數，
另以 Python 窮舉 F₂⁶ 的 1395 個三維子空間核對過。 -/

def mbit (m : Fin 512) (k : Nat) : Nat := m.val / 2 ^ k % 2

/-- 矩陣乘向量（mod 2） -/
def mv (m : Fin 512) (x : Fin 8) : Fin 8 :=
  let row (i : Nat) : Nat :=
    (mbit m (3 * i) * bit x 0 + mbit m (3 * i + 1) * bit x 1 + mbit m (3 * i + 2) * bit x 2) % 2
  f8 (row 0 + 2 * row 1 + 4 * row 2)

/-- K_φ 的元素 -/
def elem (m : Fin 512) (x : Fin 8) : Fin 8 × Fin 8 := (xo x (mv m x), mv m x)

/-- (a, b) ∈ K_φ：令 x = a ⊕ b，看是否 elem φ x = (a, b) -/
def memK (m : Fin 512) (a b : Fin 8) : Prop := elem m (xo a b) = (a, b)

instance (m : Fin 512) (a b : Fin 8) : Decidable (memK m a b) := by
  unfold memK; infer_instance

set_option maxHeartbeats 0 in
/-- φ 是線性的（32768 種情形，交給核心直接計算） -/
theorem mv_linear : ∀ m : Fin 512, ∀ x y : Fin 8, mv m (xo x y) = xo (mv m x) (mv m y) := by
  decide +kernel

/-- K_φ ∩ Δ = {0}：互補 -/
theorem K_meets_diag_trivially : ∀ m : Fin 512, ∀ x : Fin 8,
    (elem m x).1 = (elem m x).2 → x = 0 := by decide

/-- K_φ 的每個元素都在 K_φ 裡（由 x = a ⊕ b 還原） -/
theorem elem_mem : ∀ m : Fin 512, ∀ x : Fin 8, memK m (elem m x).1 (elem m x).2 := by decide

/-- 上卦方向與下卦方向都在這一族裡 -/
theorem upper_lower_in_family :
    (∀ x : Fin 8, elem 0 x = (x, 0)) ∧ (∀ x : Fin 8, elem 273 x = (0, x)) := by decide

/-- 由 elem 還原 x -/
theorem elem_recover : ∀ m : Fin 512, ∀ x : Fin 8, xo (elem m x).1 (elem m x).2 = x := by decide

/-- 由三個基底的像還原矩陣 -/
def decode (c1 c2 c4 : Fin 8) : Nat :=
  let col (c : Fin 8) (j : Nat) : Nat := bit c 0 * 2 ^ j + bit c 1 * 2 ^ (3 + j) + bit c 2 * 2 ^ (6 + j)
  col c1 0 + col c2 1 + col c4 2

theorem decode_mv : ∀ m : Fin 512, decode (mv m 1) (mv m 2) (mv m 4) = m.val := by decide

/-- 不同的 φ 給出不同的映射 -/
theorem mv_injective (m m' : Fin 512) (h : ∀ x, mv m x = mv m' x) : m = m' := by
  apply Fin.ext
  rw [← decode_mv m, ← decode_mv m', h 1, h 2, h 4]

/-- 不同的 φ 給出不同的子空間 K_φ：至少有 512 個互補子空間 -/
theorem K_injective (m m' : Fin 512) (h : ∀ a b : Fin 8, memK m a b ↔ memK m' a b) : m = m' := by
  apply mv_injective
  intro x
  have h1 : memK m' (elem m x).1 (elem m x).2 := (h _ _).mp (elem_mem m x)
  unfold memK at h1
  rw [elem_recover m x] at h1
  exact (congrArg Prod.snd h1).symm

/-! ## 9. XOR 與共軛 -/

/-- XOR 同一個卦做兩次回原樣（對合） -/
theorem xor_involution : ∀ a m : Fin 8, xo (xo a m) m = a := by decide

/-- XOR 可交換，所以在 XOR 自己的群裡共軛沒有內容：b·a·b⁻¹ = a -/
theorem xor_conj_trivial : ∀ a b : Fin 8, xo (xo b a) b = a := by decide

/-- 八種翻法裡，只有 XOR 坤保持每一卦的陽爻數（不動），只有 XOR 乾把 k 換成 3 − k（3 ↔ 3̄） -/
theorem xor_layers : ∀ m : Fin 8,
    ((∀ a : Fin 8, yao (xo a m) = yao a) ↔ m = 0) ∧
    ((∀ a : Fin 8, yao (xo a m) = 3 - yao a) ↔ m = 7) := by decide

/-- 交換初、二爻 -/
def swap12 (a : Fin 8) : Fin 8 := f8 (4 * bit a 1 + 2 * bit a 2 + bit a 0)

/-- 在立方體的對稱群裡：交換初二 · 翻初 · 交換初二 = 翻二。做共軛的是爻位交換，不是 XOR -/
theorem conj_by_swap : ∀ a : Fin 8, swap12 (xo (swap12 a) 4) = xo a 2 := by decide

/-- 六十四卦用 0..63 表示（下卦在高三位、上卦在低三位，初爻為最高位） -/
def rev6 (h : Nat) : Nat :=
  (h / 32 % 2) + 2 * (h / 16 % 2) + 4 * (h / 8 % 2) + 8 * (h / 4 % 2) + 16 * (h / 2 % 2) + 32 * (h % 2)

/-- 綜卦（六爻上下顛倒）不是 XOR：沒有任何一個固定的卦 m 能讓 64 卦的綜卦都等於 h ⊕ m -/
theorem zong_not_xor :
    (List.range 64).all (fun m => (List.range 64).any (fun h => rev6 h != (h ^^^ m))) = true := by
  decide

end CubeToSU3.Dagua
