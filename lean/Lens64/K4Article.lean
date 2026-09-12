import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# 澄序《K4 的静态闭包与动态规范形》—— 直接形式化伴随（第一组）
本文件覆盖正文中的若干直接命题，不是完整形式化。
-/
namespace K4Article

/-! ## 命题 2（无典范配对）：任意 f : S ≃ D 都被 D 上某个置换破坏——即不存在对 Sym(D) 等变的双射。
文中是元陈述「由裸结构唯一确定」，Lean 里必须落成一个可判定命题：
∀ f, ∃ σ, σ ∘ f ≠ f。有限，decide。 -/
theorem no_canonical_pairing :
    ∀ f : Fin 4 ≃ Fin 4, ∃ σ : Equiv.Perm (Fin 4), σ.trans f ≠ f ∨ f.trans σ ≠ f := by
  decide

/-! ## §2.3 的秩条件投影
这里的 `R4` 只编码「秩 1、2、3、4 非空」，不等于正文 `R_4` 的完整定义。
所得结论只是该秩条件的首个满足维数，且由前件直接读出。 -/
/-- B_n 的秩 k 非空 ⇔ k ≤ n -/
def rankNonempty (n k : ℕ) : Prop := k ≤ n
def R4 (n : ℕ) : Prop := rankNonempty n 1 ∧ rankNonempty n 2 ∧ rankNonempty n 3 ∧ rankNonempty n 4
theorem R4_iff (n : ℕ) : R4 n ↔ 4 ≤ n := by unfold R4 rankNonempty; omega
theorem four_is_min_R4 : R4 4 ∧ ∀ n, R4 n → 4 ≤ n := by
  refine ⟨by unfold R4 rankNonempty; omega, fun n h => (R4_iff n).1 h⟩

/-! ## §4.2 商：size 等价不是同余（文中反例 I={e1} J={e2} K={e1}）——decide 直接核 -/
abbrev sizeEq (I J : Finset (Fin 5)) : Prop := I.card = J.card
theorem size_not_congruent :
    ∃ I J K : Finset (Fin 5), sizeEq I J ∧ ¬ sizeEq (I ∩ K) (J ∩ K) := by
  refine ⟨{0}, {1}, {0}, ?_, ?_⟩ <;> decide

/-! ## §4.2 forget 商：B_5 → B_4 由 I ↦ I ∩ E_4 给出，像集恰为 B_4（16 个），且每个像有 2 个原像（丢一比特）——decide -/
def E4 : Finset (Fin 5) := {0, 1, 2, 3}
theorem forget_image_card :
    ((Finset.univ : Finset (Finset (Fin 5))).image (· ∩ E4)).card = 16 := by decide
theorem forget_fiber_two : ∀ J ∈ (Finset.univ : Finset (Finset (Fin 5))).image (· ∩ E4),
    ((Finset.univ : Finset (Finset (Fin 5))).filter (· ∩ E4 = J)).card = 2 := by decide

/-! ## §2.2 / §4.1 计数：W_n 各阶 = 下降阶乘，n=5 合计 325（文中数字）-/
theorem W5_total :
    Fintype.card (Fin 1 ↪ Fin 5) + Fintype.card (Fin 2 ↪ Fin 5) + Fintype.card (Fin 3 ↪ Fin 5)
      + Fintype.card (Fin 4 ↪ Fin 5) + Fintype.card (Fin 5 ↪ Fin 5) = 325 := by
  simp only [Fintype.card_embedding_eq, Fintype.card_fin]; decide

/-! ## 命题 7（n ≠ 4 时 B_n ≄ B_4）：基数论证，一般 n -/
theorem B_not_iso (n : ℕ) (h : n ≠ 4) : ¬ Nonempty (Finset (Fin n) ≃ Finset (Fin 4)) := by
  rintro ⟨e⟩
  have := Fintype.card_congr e
  simp only [Fintype.card_finset, Fintype.card_fin] at this
  exact h (Nat.pow_right_injective (le_refl 2) this)

end K4Article
