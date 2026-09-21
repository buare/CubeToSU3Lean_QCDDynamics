import Mathlib

/-!
Probe: 確認這個 Mathlib 版本裡矩陣指數相關引理的確切名稱與簽名。
放在專案最外層,執行 `lake env lean ProbeExp.lean`,把輸出貼回來。
不要 import 進主專案。
-/

open Matrix

-- 矩陣指數本身
#check @Matrix.exp
#check @Matrix.exp_diagonal
#check @Matrix.exp_conj
#check @Matrix.exp_conj'

-- 反矩陣
#check @Matrix.inv_eq_right_inv
#check @Matrix.mul_nonsing_inv

-- 複數指數與三角函數
#check @Complex.exp_mul_I
#check @Real.cos_pi_div_three
#check @Real.sin_pi_div_three
#check @Real.cos_pi_sub
#check @Real.sin_pi_sub
#check @Real.mul_self_sqrt
#check @Real.sq_sqrt

-- 純量作用與對角矩陣
#check @Matrix.diagonal
#check @Matrix.smul_apply
#check @Matrix.diagonal_apply

-- 搜尋:是否還有其他 exp 相關引理
open Matrix in
example : True := trivial

#check @Matrix.exp_transpose
#check @Matrix.exp_conjTranspose
