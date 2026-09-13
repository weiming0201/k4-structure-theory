import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Ring

/-!
# 「4 在接缝层奇异」候选定理（2026-09-12，△永杰主问题「4 能否构成奇异维度」）
签名只用她文章 4.1 已有的：包含、补、秩。不引入配对结构。
主张：n = 4 是**唯一**使补集把秩 2（接缝层）送回秩 2 且无不动点的 n；由此 6 个接缝典范分成 3 对补集对（= K₄ 的 3 个完美匹配）。
-/
namespace FourSingular

/-- 秩 k 的层 -/
def rank (n k : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter fun s => s.card = k

/-! ## 一般 n：补集把秩 k 送到秩 n−k；「秩 2 自配对」⟺ n = 4 -/
theorem compl_card {n : ℕ} (s : Finset (Fin n)) : sᶜ.card = n - s.card := by
  simp [Finset.card_compl]
theorem seam_self_paired_iff (n : ℕ) : (n - 2 = 2 ∧ 2 ≤ n) ↔ n = 4 := by omega

/-! ## n = 4：补集是接缝层上的无不动点对合，恰 3 个轨道 -/
theorem compl_maps_seams_to_seams :
    ∀ s ∈ rank 4 2, sᶜ ∈ rank 4 2 := by decide
theorem compl_fixed_point_free :
    ∀ s ∈ rank 4 2, sᶜ ≠ s := by decide
theorem compl_involution :
    ∀ s ∈ rank 4 2, sᶜᶜ = s := by decide
/-- 无序补集对的个数 = 3（= K₄ 的完美匹配数 = V₄ 非平凡元数） -/
theorem three_pairs :
    ((rank 4 2).image fun s => ({s, sᶜ} : Finset (Finset (Fin 4)))).card = 3 := by decide

/-! ## n = 5：秩 2 的补是秩 3，接缝层不自配对（反例，n ≥ 5 无此结构） -/
theorem n5_seams_not_self_paired :
    ∀ s ∈ rank 5 2, sᶜ ∉ rank 5 2 := by decide

/-! ## 对称性：Sym(4) 保持「补集对」这个分法（每个置换把补集对送到补集对） -/
theorem sym_preserves_pairs :
    ∀ σ : Equiv.Perm (Fin 4), ∀ s ∈ rank 4 2,
      (s.map σ.toEmbedding)ᶜ = sᶜ.map σ.toEmbedding := by decide

/-! ## 层的大小：n=4 是接缝层严格大于点层与面层的最后一个 n（C(n,2)>n ⟺ n≥4；C(n,3)≥C(n,2) ⟺ n≥5） -/
theorem seams_dominate_4 : (rank 4 2).card > (rank 4 1).card ∧ (rank 4 2).card > (rank 4 3).card := by decide
theorem seams_tie_5 : (rank 5 2).card = (rank 5 3).card := by decide
theorem seams_lose_6 : (rank 6 2).card < (rank 6 3).card := by decide

end FourSingular
