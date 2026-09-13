import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# 闭合稳定性：M1–M5 与推论
文档：scratchpad/k4-structure-theory/closure-stability/MATHEMATICAL-FOUNDATION.md（行号见各定理注释）。
概率一律用 ℝ 上的显式权重 / 计数；不引入测度论。
* M1 均匀窗口（:173-182）  * M2 几何等待（:185-189）  * M3 无保护寿命（:194-208）
* M4 重复码（:212-226）    * M5 四坐标下限的紧性（:136-148）
* 推论 C-a … C-d（多数表决何时有益、五重 vs 三重、三重收支、等待 vs 寿命）
纪律：无 sorry、无 native_decide、无 axiom。
-/
namespace ClosureStability

open Finset

/-! ## M1 均匀窗口（:173-182） -/
section M1
variable {m : ℕ}

/-- 可接受模式集合 `V ⊆ Σᵐ` 在均匀重采样下的概率 `|V| / 2ᵐ`（:180-182） -/
noncomputable def uniformProb (V : Finset (Fin m → Bool)) : ℝ := V.card / 2 ^ m

/-- 窗口空间 `Σᵐ` 有 `2ᵐ` 个元素（:173-176 的分母） -/
theorem card_window (m : ℕ) : Fintype.card (Fin m → Bool) = 2 ^ m := by
  simp

/-- 单模式 `P(W = w) = 2⁻ᵐ`（:176-178） -/
theorem uniformProb_singleton (w : Fin m → Bool) : uniformProb {w} = 1 / 2 ^ m := by
  simp [uniformProb]

/-- 全空间概率为 1（归一化） -/
theorem uniformProb_univ : uniformProb (Finset.univ : Finset (Fin m → Bool)) = 1 := by
  rw [uniformProb, Finset.card_univ, card_window]
  push_cast
  exact div_self (by positivity)

theorem uniformProb_nonneg (V : Finset (Fin m → Bool)) : 0 ≤ uniformProb V := by
  unfold uniformProb; positivity

theorem uniformProb_le_one (V : Finset (Fin m → Bool)) : uniformProb V ≤ 1 := by
  unfold uniformProb
  rw [div_le_one (by positivity)]
  have h := Finset.card_le_univ V
  rw [card_window] at h
  exact_mod_cast h

theorem uniformProb_pos {V : Finset (Fin m → Bool)} (hV : V.Nonempty) : 0 < uniformProb V := by
  unfold uniformProb
  have : (0 : ℝ) < V.card := by exact_mod_cast hV.card_pos
  positivity

end M1

/-! ## M2 几何等待（:185-189）
首次命中的等待轮数 `T ∈ {1,2,…}`，`P(T = k) = q (1-q)^(k-1)`。下面用 `k = j+1` 重新编号：
`E[T] = Σ_{j≥0} (j+1) q (1-q)^j = 1/q`。注意 `q = 1` 时 `1-q = 0`，`‖0‖ < 1` 仍成立，
所以不必单独处理。-/
section M2

/-- 几何分布归一化：`Σ_j q (1-q)^j = 1` -/
theorem geometric_mass_hasSum {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) :
    HasSum (fun j : ℕ => q * (1 - q) ^ j) 1 := by
  have hB := hasSum_geometric_of_lt_one (r := 1 - q) (by linarith) (by linarith)
  have hC := hB.mul_left q
  rwa [sub_sub_cancel, mul_inv_cancel₀ h0.ne'] at hC

/-- 几何等待的期望（HasSum 形式）：`Σ_j (j+1) q (1-q)^j = 1/q`（:187-189） -/
theorem geometric_wait_hasSum {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * q * (1 - q) ^ j) (1 / q) := by
  have hr : ‖(1 - q)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  -- Σ j r^j = r/(1-r)²  与  Σ r^j = (1-r)⁻¹
  have hA := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr
  have hB := hasSum_geometric_of_lt_one (r := 1 - q) (by linarith) (by linarith)
  have hC := (hA.add hB).mul_left q
  rw [sub_sub_cancel] at hC
  have hq : q ≠ 0 := h0.ne'
  have hval : q * ((1 - q) / q ^ 2 + q⁻¹) = 1 / q := by
    field_simp
    ring
  have hfun : (fun j : ℕ => ((j : ℝ) + 1) * q * (1 - q) ^ j)
      = fun i : ℕ => q * ((i : ℝ) * (1 - q) ^ i + (1 - q) ^ i) := by
    funext j; ring
  rw [hval] at hC
  rw [hfun]
  exact hC

/-- 几何等待的期望（tsum 形式）：`Σ' j, (j+1) q (1-q)^j = 1/q`（:187-189） -/
theorem geometric_wait_tsum {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) * q * (1 - q) ^ j = 1 / q :=
  (geometric_wait_hasSum h0 h1).tsum_eq

/-- `E[T] = 2ᵐ / |V|`（:187-189）：把 `q = |V|/2ᵐ` 代入 -/
theorem expected_wait {m : ℕ} {V : Finset (Fin m → Bool)} (hV : V.Nonempty) :
    ∑' j : ℕ, ((j : ℝ) + 1) * uniformProb V * (1 - uniformProb V) ^ j = 2 ^ m / V.card := by
  rw [geometric_wait_tsum (uniformProb_pos hV) (uniformProb_le_one V), uniformProb, one_div_div]

end M2

/-! ## M3 无保护寿命（:194-208） -/
section M3
variable {m : ℕ}

/-- `m` 个独立 `p`-翻转的权重：`w(x) = ∏ᵢ (x i ? p : 1-p)`（:196-197 的独立翻转模型） -/
noncomputable def w (p : ℝ) (x : Fin m → Bool) : ℝ := ∏ i, if x i then p else (1 - p)

/-- 权重归一化：`Σ_x w(x) = 1`（`∏ᵢ (p + (1-p)) = 1`） -/
theorem w_sum (p : ℝ) (m : ℕ) : ∑ x : Fin m → Bool, w p x = 1 := by
  unfold w
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset Bool))
    (fun _ b => if b then p else (1 - p))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

/-- 一步无翻转（`x ≡ false`）的权重 `= (1-p)ᵐ = s₀`（:198-200） -/
theorem w_none (p : ℝ) : w p (fun _ : Fin m => false) = (1 - p) ^ m := by
  simp [w]

/-- `s₀ < 1`：`0 < p ≤ 1`、`m ≥ 1` 时一步保持有效的概率严格小于 1 -/
theorem s0_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hm : m ≠ 0) : (1 - p) ^ m < 1 :=
  pow_lt_one₀ (by linarith) (by linarith) hm

/-- 无保护寿命 `L ∈ {1,2,…}`，`P(L = k) = s₀^(k-1)(1-s₀)`，重新编号 `k = j+1`：
`E[L] = Σ_j (j+1)(1-s₀) s₀^j = 1/(1-s₀)`（:202-206）。由 M2 取 `q = 1 - s₀`。 -/
theorem expected_lifetime {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hm : m ≠ 0) :
    ∑' j : ℕ, ((j : ℝ) + 1) * (1 - (1 - p) ^ m) * ((1 - p) ^ m) ^ j = 1 / (1 - (1 - p) ^ m) := by
  have hq0 : 0 < 1 - (1 - p) ^ m := by linarith [s0_lt_one hp0 hp1 hm]
  have hq1 : 1 - (1 - p) ^ m ≤ 1 := by linarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 - p) m]
  have h := geometric_wait_tsum hq0 hq1
  simpa only [sub_sub_cancel] using h

end M3

/-! ## M4 重复码（:212-226） -/
section M4

/-- 奇数 `r` 重复码、多数表决的单步解码失败概率
`P_fail(r,p) = Σ_{k=(r+1)/2}^{r} C(r,k) pᵏ (1-p)^(r-k)`（:216-218） -/
noncomputable def pFail (r : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc ((r + 1) / 2) r, (r.choose k : ℝ) * p ^ k * (1 - p) ^ (r - k)

theorem Icc_two_three : Finset.Icc ((3 + 1) / 2) 3 = ({2, 3} : Finset ℕ) := by decide
theorem Icc_three_five : Finset.Icc ((5 + 1) / 2) 5 = ({3, 4, 5} : Finset ℕ) := by decide

/-- (a) `P_fail(3,p) = 3p² - 2p³`（:216-218 展开） -/
theorem pFail_three (p : ℝ) : pFail 3 p = 3 * p ^ 2 - 2 * p ^ 3 := by
  rw [pFail, Icc_two_three, Finset.sum_pair (by norm_num)]
  have c32 : Nat.choose 3 2 = 3 := by decide
  have c33 : Nat.choose 3 3 = 1 := by decide
  rw [c32, c33]
  push_cast
  ring

/-- (a) `P_fail(5,p) = 10p³ - 15p⁴ + 6p⁵`（:216-218 展开） -/
theorem pFail_five (p : ℝ) : pFail 5 p = 10 * p ^ 3 - 15 * p ^ 4 + 6 * p ^ 5 := by
  rw [pFail, Icc_three_five, Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_singleton]
  have c53 : Nat.choose 5 3 = 10 := by decide
  have c54 : Nat.choose 5 4 = 5 := by decide
  have c55 : Nat.choose 5 5 = 1 := by decide
  rw [c53, c54, c55]
  push_cast
  ring

/-- (b) 上界 `P_fail(r,p) ≤ 2ʳ p^((r+1)/2)`（:220-222 的 `O(p^((r+1)/2))`）：
每项 `pᵏ ≤ p^((r+1)/2)`（`k ≥ (r+1)/2`，`p ≤ 1`），`(1-p)^(r-k) ≤ 1`，`Σ C(r,k) ≤ 2ʳ`。 -/
theorem pFail_le (r : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    pFail r p ≤ 2 ^ r * p ^ ((r + 1) / 2) := by
  have h1p : 0 ≤ 1 - p := by linarith
  unfold pFail
  calc ∑ k ∈ Finset.Icc ((r + 1) / 2) r, (r.choose k : ℝ) * p ^ k * (1 - p) ^ (r - k)
      ≤ ∑ k ∈ Finset.Icc ((r + 1) / 2) r, (r.choose k : ℝ) * p ^ ((r + 1) / 2) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Icc] at hk
        have e1 : p ^ k ≤ p ^ ((r + 1) / 2) := pow_le_pow_of_le_one hp0 hp1 hk.1
        have e2 : (1 - p) ^ (r - k) ≤ 1 := pow_le_one₀ h1p (by linarith)
        have e3 : 0 ≤ (r.choose k : ℝ) := by positivity
        have e4 : 0 ≤ p ^ k := pow_nonneg hp0 k
        calc (r.choose k : ℝ) * p ^ k * (1 - p) ^ (r - k)
            ≤ (r.choose k : ℝ) * p ^ k * 1 := by gcongr
          _ = (r.choose k : ℝ) * p ^ k := by ring
          _ ≤ (r.choose k : ℝ) * p ^ ((r + 1) / 2) := by gcongr
    _ = (∑ k ∈ Finset.Icc ((r + 1) / 2) r, (r.choose k : ℝ)) * p ^ ((r + 1) / 2) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ)) * p ^ ((r + 1) / 2) := by
        have hsub : Finset.Icc ((r + 1) / 2) r ⊆ Finset.range (r + 1) := by
          intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_range]
          omega
        have hpe : 0 ≤ p ^ ((r + 1) / 2) := pow_nonneg hp0 _
        apply mul_le_mul_of_nonneg_right _ hpe
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intros; positivity
    _ = 2 ^ r * p ^ ((r + 1) / 2) := by
        congr 1
        exact_mod_cast Nat.sum_range_choose r

/-- (c) 下界：取 `k = (r+1)/2` 这一项（:220-222 的 `Ω(p^((r+1)/2))`），
与 (b) 合起来即文档的 `Θ(p^((r+1)/2))`。 -/
theorem pFail_ge (r : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (r.choose ((r + 1) / 2) : ℝ) * p ^ ((r + 1) / 2) * (1 - p) ^ (r - (r + 1) / 2) ≤ pFail r p := by
  have h1p : 0 ≤ 1 - p := by linarith
  unfold pFail
  apply Finset.single_le_sum (f := fun k => (r.choose k : ℝ) * p ^ k * (1 - p) ^ (r - k))
  · intro k _
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp0 _)) (pow_nonneg h1p _)
  · rw [Finset.mem_Icc]; omega

/-- `P_fail` 非负（`0 ≤ p ≤ 1`） -/
theorem pFail_nonneg (r : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ pFail r p := by
  have h1p : 0 ≤ 1 - p := by linarith
  unfold pFail
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp0 _)) (pow_nonneg h1p _)

end M4

/-! ## M5 四坐标下限的紧性（:136-148）
文档定理 1：若 `m` 个二值位点对全部十六种剖面保真，则 `m ≥ 4`（下界已在别处证）。
这里补紧性：`encode := profile` 本身就是 `m = 4` 的保真编码，所以「至少四」可达。-/
section M5
variable {Z E : Type*}

/-- 剖面保真（:133 前件 2）：编码相同的状态具有相同剖面 -/
def ProfileFaithful (profile : Z → Fin 4 → Bool) (encode : Z → E) : Prop :=
  ∀ x y, encode x = encode y → profile x = profile y

/-- 紧性：`profile` 自身是 `m = 4` 个二值位点上的保真编码 -/
theorem profileFaithful_self (profile : Z → Fin 4 → Bool) : ProfileFaithful profile profile :=
  fun _ _ h => h

/-- `m = 4` 时位点空间恰有 16 个点（:138-141 `{0,1}⁴`） -/
theorem card_profile_space : Fintype.card (Fin 4 → Bool) = 16 := by
  rw [card_window]; norm_num

end M5

/-! ## 推论 -/
section Corollaries

/-! ### C-a 多数表决有益 ⟺ `p < 1/2`
`p - P_fail(3,p) = p (1-p)(1-2p)`。 -/

theorem majority_helps {p : ℝ} (h0 : 0 < p) (h1 : p < 1 / 2) : pFail 3 p < p := by
  rw [pFail_three]
  nlinarith [mul_pos h0 (mul_pos (by linarith : 0 < 1 - 2 * p) (by linarith : 0 < 1 - p))]

theorem majority_hurts {p : ℝ} (h0 : 1 / 2 < p) (h1 : p < 1) : p < pFail 3 p := by
  rw [pFail_three]
  have hp : 0 < p := by linarith
  nlinarith [mul_pos hp (mul_pos (by linarith : 0 < 2 * p - 1) (by linarith : 0 < 1 - p))]

theorem pFail_three_half : pFail 3 (1 / 2) = 1 / 2 := by
  rw [pFail_three]; norm_num

/-! ### C-b 五重优于三重同样只在 `p < 1/2`
`P_fail(5,p) - P_fail(3,p) = 3 p² (1-p)² (2p-1)`。 -/

theorem pFail_five_sub_three (p : ℝ) :
    pFail 5 p - pFail 3 p = 3 * p ^ 2 * (1 - p) ^ 2 * (2 * p - 1) := by
  rw [pFail_five, pFail_three]; ring

theorem five_better_than_three {p : ℝ} (h0 : 0 < p) (h1 : p < 1 / 2) : pFail 5 p < pFail 3 p := by
  have h1p : 0 < 1 - p := by linarith
  have hpos : 0 < 3 * p ^ 2 * (1 - p) ^ 2 := by positivity
  have hneg : 3 * p ^ 2 * (1 - p) ^ 2 * (2 * p - 1) < 0 :=
    mul_neg_of_pos_of_neg hpos (by linarith)
  linarith [pFail_five_sub_three p]

theorem five_worse_than_three {p : ℝ} (h0 : 1 / 2 < p) (h1 : p < 1) : pFail 3 p < pFail 5 p := by
  have h1p : 0 < 1 - p := by linarith
  have hp : 0 < p := by linarith
  have hpos : 0 < 3 * p ^ 2 * (1 - p) ^ 2 := by positivity
  have hpos' : 0 < 3 * p ^ 2 * (1 - p) ^ 2 * (2 * p - 1) :=
    mul_pos hpos (by linarith)
  linarith [pFail_five_sub_three p]

theorem pFail_five_half : pFail 5 (1 / 2) = pFail 3 (1 / 2) := by
  rw [pFail_five, pFail_three]; norm_num

/-! ### C-c 三重复码的寿命 / 存储收支
单位 `m = 1`：无保护 `E[L₁] = 1/p`，三重 `E[L₃] = 1/P_fail(3,p)`，存储成本 3×。
`3/p ≤ 1/P_fail(3,p) ⟺ 6p² - 9p + 1 ≥ 0`，平衡点 `(9-√57)/12 ≈ 0.1208`（不证）。 -/

theorem pFail_three_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 0 < pFail 3 p := by
  rw [pFail_three]
  nlinarith [mul_pos (pow_pos h0 2) (by linarith : 0 < 3 - 2 * p)]

/-- `0 < p ≤ 1/9` 时寿命增益 ≥ 存储成本 3× -/
theorem triple_pays_off {p : ℝ} (h0 : 0 < p) (h9 : p ≤ 1 / 9) : 3 * (1 / p) ≤ 1 / pFail 3 p := by
  have hF : 0 < pFail 3 p := pFail_three_pos h0 (by linarith)
  rw [mul_one_div, le_div_iff₀ hF, div_mul_eq_mul_div, div_le_iff₀ h0, pFail_three]
  nlinarith [mul_nonneg h0.le (by linarith : 0 ≤ 1 - 9 * p), mul_nonneg h0.le (sq_nonneg p)]

/-- 反例：`p = 1/8` 时不成立（`1/P_fail = 256/11 < 24 = 3/p`），平衡点在 `1/9` 与 `1/8` 之间 -/
theorem triple_fails_at_eighth : ¬ (3 * (1 / (1 / 8 : ℝ)) ≤ 1 / pFail 3 (1 / 8)) := by
  rw [pFail_three]; norm_num

/-! ### C-d 等待与寿命的对照
`E[T] = 2ᵐ/|V|` 随 `m` 指数增长（M2）；`E[L] = 1/(1-(1-p)ᵐ)` 只有多项式级：
`m p (1-p)^(m-1) ≤ 1-(1-p)ᵐ ≤ m p`，故 `1/(m p) ≤ E[L] ≤ 1/(m p (1-p)^(m-1))`。 -/

/-- 归纳核心：`0 ≤ s ≤ 1` 时 `(n+1)(1-s) sⁿ ≤ 1 - s^(n+1)` -/
theorem one_sub_pow_ge_aux {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ n : ℕ, ((n : ℝ) + 1) * (1 - s) * s ^ n ≤ 1 - s ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have ih := one_sub_pow_ge_aux hs0 hs1 n
    have hmono : s ^ (n + 1) ≤ s ^ n := pow_le_pow_of_le_one hs0 hs1 (by omega)
    have hkey : 0 ≤ ((n : ℝ) + 1) * (1 - s) * (s ^ n - s ^ (n + 1)) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    have e1 : s ^ (n + 1) = s ^ n * s := pow_succ s n
    have e2 : s ^ (n + 1 + 1) = s ^ (n + 1) * s := pow_succ s (n + 1)
    push_cast
    nlinarith [ih, hkey, e1, e2]

/-- 下界 `m p (1-p)^(m-1) ≤ 1 - (1-p)ᵐ`（`m ≥ 1`，`0 ≤ p ≤ 1`） -/
theorem one_sub_pow_ge {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (hm : m ≠ 0) :
    (m : ℝ) * p * (1 - p) ^ (m - 1) ≤ 1 - (1 - p) ^ m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h := one_sub_pow_ge_aux (s := 1 - p) (by linarith) (by linarith) n
  simp only [Nat.add_sub_cancel, sub_sub_cancel] at h ⊢
  push_cast
  exact h

/-- 上界 `1 - (1-p)ᵐ ≤ m p`（Bernoulli，mathlib `one_add_mul_le_pow`） -/
theorem one_sub_pow_le {p : ℝ} (hp : p ≤ 2) (m : ℕ) : 1 - (1 - p) ^ m ≤ m * p := by
  have h := one_add_mul_le_pow (a := -p) (by linarith) m
  have e : (1 : ℝ) + -p = 1 - p := by ring
  rw [e] at h
  linarith

/-- `E[L] ≥ 1/(m p)`：寿命至少与 `1/(mp)` 同阶，不是指数 -/
theorem lifetime_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {m : ℕ} (hm : m ≠ 0) :
    1 / ((m : ℝ) * p) ≤ 1 / (1 - (1 - p) ^ m) := by
  have hq0 : 0 < 1 - (1 - p) ^ m := by linarith [s0_lt_one hp0 hp1 hm]
  exact one_div_le_one_div_of_le hq0 (one_sub_pow_le (by linarith) m)

/-- `E[L] ≤ 1/(m p (1-p)^(m-1))` -/
theorem lifetime_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {m : ℕ} (hm : m ≠ 0) :
    1 / (1 - (1 - p) ^ m) ≤ 1 / ((m : ℝ) * p * (1 - p) ^ (m - 1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have h1p : 0 < 1 - p := by linarith
  have hd : 0 < (m : ℝ) * p * (1 - p) ^ (m - 1) := by positivity
  exact one_div_le_one_div_of_le hd (one_sub_pow_ge hp0.le hp1.le hm)

end Corollaries

end ClosureStability
