import Mathlib

/-!
探針之二:第二階段還需要確認的名稱。放專案最外層,`lake env lean ProbeExp2.lean`。
哪一行是 unknown constant,把訊息貼回來即可。
-/

-- 純量指數:NormedSpace.exp ℂ 與 Complex.exp 的關係
#check @Complex.exp_eq_exp_ℂ
#check @Complex.exp_mul_I
#check @Complex.ofReal_cos
#check @Complex.ofReal_sin
#check @Complex.cos_neg
#check @Complex.sin_neg

-- Pi 型別上的指數(Matrix.exp_diagonal 的右邊會用到)
#check @Pi.exp_apply

-- 可逆性
#check @Matrix.isUnit_iff_isUnit_det
#check @Matrix.isUnit_det_of_right_inverse

-- 純量作用與乘法的搬移
#check @Matrix.smul_mul
#check @Matrix.mul_smul

-- 實數平方根
#check @Real.sqrt_pos
