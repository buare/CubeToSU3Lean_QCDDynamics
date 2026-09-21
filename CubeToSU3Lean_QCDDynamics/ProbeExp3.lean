import Mathlib

/-!
探針之三:找出「Pi 型別上的指數是逐點的」那條引理的正確名稱。
放專案最外層,`lake env lean ProbeExp3.lean`,把輸出全部貼回來。
-/

-- 主要目標:讓 Lean 自己找出引理名稱(會以 "Try this: exact ..." 印出)
example (v : Fin 3 → ℂ) (i : Fin 3) :
    NormedSpace.exp ℂ v i = NormedSpace.exp ℂ (v i) := by
  exact?

-- 備案一:也許 simp 就能處理
example (v : Fin 3 → ℂ) (i : Fin 3) :
    NormedSpace.exp ℂ v i = NormedSpace.exp ℂ (v i) := by
  simp

-- 備案二:幾個可能的名字
#check @Pi.exp_def
#check @NormedSpace.exp_pi
#check @NormedSpace.Pi.exp_apply

open NormedSpace in
#check @Pi.exp_apply
