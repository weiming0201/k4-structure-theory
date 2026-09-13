import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
import Lens64.FourSingular

/-!
# 复杂度奇异点在 4→5（2026-09-12，接 FourSingular）
`S₄` 可解、`S₅` 不可解；Klein 四元群 `V₄` 作为显式中间项。
接缝层的 3 对补集对（FourSingular.three_pairs）= K₄ 的 3 个完美匹配 = `V₄` 的 3 个非幺元。

导出列：S₄ ⊳ A₄ ⊳ V₄ ⊳ 1。
* ⁅S₄,S₄⁆ ≤ A₄：一般定理（sign 是到交换群 ℤˣ 的同态，换位子落在核里）。
* ⁅A₄,A₄⁆ ≤ V₄、⁅V₄,V₄⁆ = 1、V₄ 正规：有限，`decide +kernel`（sign 在 Fin 4 上核内可算）。
* S₅：mathlib `Equiv.Perm.not_isSolvable_fin_5`。

纪律：无 sorry、无 native_decide、无 axiom。
-/
namespace FourSingular
open Equiv Equiv.Perm
open scoped commutatorElement

/-! ## V₄：三个双换位 -/

/-- (0 1)(2 3)：固定接缝对 {{0,1},{2,3}} -/
def dt01 : Perm (Fin 4) := swap 0 1 * swap 2 3
/-- (0 2)(1 3)：固定接缝对 {{0,2},{1,3}} -/
def dt02 : Perm (Fin 4) := swap 0 2 * swap 1 3
/-- (0 3)(1 2)：固定接缝对 {{0,3},{1,2}} -/
def dt03 : Perm (Fin 4) := swap 0 3 * swap 1 2

/-- V₄ 的载体谓词（可判定） -/
def inV4 (σ : Perm (Fin 4)) : Prop := σ = 1 ∨ σ = dt01 ∨ σ = dt02 ∨ σ = dt03

instance : DecidablePred inV4 := fun σ =>
  inferInstanceAs (Decidable (σ = 1 ∨ σ = dt01 ∨ σ = dt02 ∨ σ = dt03))

theorem inV4_mul : ∀ a b : Perm (Fin 4), inV4 a → inV4 b → inV4 (a * b) := by decide +kernel
theorem inV4_inv : ∀ a : Perm (Fin 4), inV4 a → inV4 a⁻¹ := by decide +kernel

/-- Klein 四元群 V₄ ≤ S₄，显式载体 {1, (01)(23), (02)(13), (03)(12)} -/
def V4 : Subgroup (Perm (Fin 4)) where
  carrier := {σ | inV4 σ}
  one_mem' := Or.inl rfl
  mul_mem' := fun ha hb => inV4_mul _ _ ha hb
  inv_mem' := fun ha => inV4_inv _ ha

theorem mem_V4 (σ : Perm (Fin 4)) : σ ∈ V4 ↔ inV4 σ := Iff.rfl

instance : DecidablePred (· ∈ V4) := fun σ => inferInstanceAs (Decidable (inV4 σ))

theorem V4_conj : ∀ n, n ∈ V4 → ∀ g : Perm (Fin 4), g * n * g⁻¹ ∈ V4 := by decide +kernel

/-- V₄ ⊴ S₄ -/
theorem V4_normal : V4.Normal := ⟨V4_conj⟩

theorem V4_card_fintype : Fintype.card V4 = 4 := by decide +kernel

theorem V4_card : Nat.card V4 = 4 := by
  rw [Nat.card_eq_fintype_card]; exact V4_card_fintype

/-- V₄ 交换 -/
theorem V4_comm : ∀ a ∈ V4, ∀ b ∈ V4, a * b = b * a := by decide +kernel

/-! ## V₄ 的三个非幺元 = 接缝层的三对补集对 -/

/-- 非幺元 ⟺ 无不动点对合（双换位） -/
theorem V4_nonid_iff_fpf_involution :
    ∀ σ : Perm (Fin 4), (σ ∈ V4 ∧ σ ≠ 1) ↔ (σ * σ = 1 ∧ ∀ x, σ x ≠ x) := by decide +kernel

/-- 非幺元 ⟺ 存在接缝 s（秩 2），σ 在 s 内互换两点、在 sᶜ 内互换两点（= 把补集对 {s,sᶜ} 当作完美匹配） -/
theorem V4_is_seam_pairs :
    ∀ σ : Perm (Fin 4), (σ ∈ V4 ∧ σ ≠ 1) ↔
      ∃ s ∈ rank 4 2, (∀ x ∈ s, σ x ∈ s ∧ σ x ≠ x) ∧ (∀ x ∈ sᶜ, σ x ∈ sᶜ ∧ σ x ≠ x) := by
  decide +kernel

/-- σ 保持（作为集合）的接缝 -/
def fixedSeams (σ : Perm (Fin 4)) : Finset (Finset (Fin 4)) :=
  (rank 4 2).filter fun s => s.map σ.toEmbedding = s

/-- 每个非幺元固定的接缝恰是一对补集对 {s, sᶜ} -/
theorem V4_fixedSeams_pair :
    ∀ σ ∈ V4, σ ≠ 1 → ∃ s ∈ rank 4 2, fixedSeams σ = {s, sᶜ} := by decide +kernel

/-- V₄ ∖ {1} 经 fixedSeams 的像 = FourSingular.three_pairs 里的那 3 对补集对 -/
theorem V4_fixedSeams_image :
    ((Finset.univ.filter (· ∈ V4)).erase 1).image fixedSeams
      = (rank 4 2).image (fun s => ({s, sᶜ} : Finset (Finset (Fin 4)))) := by decide +kernel

/-- fixedSeams 在 V₄ ∖ {1} 上单射：非幺元 ↔ 补集对 是双射 -/
theorem V4_fixedSeams_injOn :
    ∀ σ ∈ V4, ∀ τ ∈ V4, σ ≠ 1 → τ ≠ 1 → fixedSeams σ = fixedSeams τ → σ = τ := by decide +kernel

theorem V4_three_nonid : ((Finset.univ.filter (· ∈ V4)).erase 1).card = 3 := by decide +kernel

/-! ## 导出列 S₄ ⊳ A₄ ⊳ V₄ ⊳ 1 -/

instance : DecidablePred (· ∈ alternatingGroup (Fin 4)) := fun g => sign.decidableMemKer g

/-- V₄ ≤ A₄（双换位是偶置换） -/
theorem V4_mem_A4 : ∀ σ ∈ V4, σ ∈ alternatingGroup (Fin 4) := by decide +kernel
theorem V4_le_A4 : V4 ≤ alternatingGroup (Fin 4) := fun σ hσ => V4_mem_A4 σ hσ

theorem A4_card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

/-- ⁅S₄,S₄⁆ ≤ A₄：换位子在 sign 的核里（一般定理，不用枚举） -/
theorem commutator_top_le_A4 :
    ⁅(⊤ : Subgroup (Perm (Fin 4))), ⊤⁆ ≤ alternatingGroup (Fin 4) :=
  Abelianization.commutator_subset_ker sign

theorem comm_A4_mem_V4 :
    ∀ g ∈ alternatingGroup (Fin 4), ∀ h ∈ alternatingGroup (Fin 4), ⁅g, h⁆ ∈ V4 := by
  decide +kernel

/-- ⁅A₄,A₄⁆ ≤ V₄ -/
theorem commutator_A4_le_V4 : ⁅alternatingGroup (Fin 4), alternatingGroup (Fin 4)⁆ ≤ V4 :=
  Subgroup.commutator_le.mpr comm_A4_mem_V4

theorem comm_V4_eq_one : ∀ g ∈ V4, ∀ h ∈ V4, ⁅g, h⁆ = 1 := by decide +kernel

/-- ⁅V₄,V₄⁆ = 1 -/
theorem commutator_V4_eq_bot : ⁅V4, V4⁆ = ⊥ :=
  le_bot_iff.mp (Subgroup.commutator_le.mpr fun g hg h hh =>
    Subgroup.mem_bot.mpr (comm_V4_eq_one g hg h hh))

theorem derivedSeries_S4_one_le : derivedSeries (Perm (Fin 4)) 1 ≤ alternatingGroup (Fin 4) :=
  commutator_top_le_A4

theorem derivedSeries_S4_two_le : derivedSeries (Perm (Fin 4)) 2 ≤ V4 :=
  (Subgroup.commutator_mono derivedSeries_S4_one_le derivedSeries_S4_one_le).trans
    commutator_A4_le_V4

/-- 导出列第 3 项为平凡群 -/
theorem derivedSeries_S4_three : derivedSeries (Perm (Fin 4)) 3 = ⊥ := by
  apply le_bot_iff.mp
  have h : derivedSeries (Perm (Fin 4)) 3 ≤ ⁅V4, V4⁆ :=
    Subgroup.commutator_mono derivedSeries_S4_two_le derivedSeries_S4_two_le
  rwa [commutator_V4_eq_bot] at h

/-- S₄ 可解 -/
theorem s4_solvable : Group.IsSolvable (Perm (Fin 4)) := ⟨⟨3, derivedSeries_S4_three⟩⟩

/-- S₅ 不可解（mathlib） -/
theorem s5_not_solvable : ¬ Group.IsSolvable (Perm (Fin 5)) := Equiv.Perm.not_isSolvable_fin_5

/-- 奇异点：4 可解，5 不可解 -/
theorem singularity_4_5 :
    Group.IsSolvable (Perm (Fin 4)) ∧ ¬ Group.IsSolvable (Perm (Fin 5)) :=
  ⟨s4_solvable, s5_not_solvable⟩

/-! ## 复杂度侧的两条 decide -/

/-- n ≤ 10：秩 2 层是唯一最大层（C(n,2) > C(n,k) 对所有 k ≠ 2）⟺ n = 4 -/
theorem rank2_unique_max_iff :
    ∀ n, n ≤ 10 → ((∀ k, k ≤ n → k ≠ 2 → n.choose k < n.choose 2) ↔ n = 4) := by decide

/-- 1 ≤ n ≤ 10：Σ_{k=1..n} n^{(k)}（降阶乘）= n·2ⁿ ⟺ n = 4（4+12+24+24 = 64 = 4·16） -/
theorem descFactorial_sum_iff :
    ∀ n, 1 ≤ n → n ≤ 10 →
      ((∑ k ∈ Finset.Icc 1 n, n.descFactorial k) = n * 2 ^ n ↔ n = 4) := by decide

end FourSingular
