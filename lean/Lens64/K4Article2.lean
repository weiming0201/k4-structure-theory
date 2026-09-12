import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Extension.Linear
import Lens64.Cycles

/-!
# 澄序《K4 的静态闭包与动态规范形》—— 直接形式化伴随（第二组）
对应正文：`../K4-MATHEMATICAL-STRUCTURE-CANDIDATE.md`；定位以章节和命题名称为准。
第一组（命题 2、§2.3 的秩条件投影、§4.2 商、W_5、命题 7）在
`Lens64/K4Article.lean`。
本批：§1.1 静态基、命题 1、§2.1/2.2 计数、命题 4、命题 5、定理 2、§4.3、命题 6。
纪律：无 sorry、无 native_decide、无 axiom；有限的用 decide，一般 n 的走 mathlib。
-/
namespace K4Article

/-! ## §1.1 静态基
正文允许每个面有各自的 `V_i`；这里为了直接重排而采用共同值域 `V`，因此是正文定义的
同值域特化，不声称已经形式化异质值域的一般情形。-/
section StaticBase
variable {U V W : Type*} {n : ℕ}

/-- §1.1 的联合观察 `F_S(x) = (s_1 x, …, s_n x)` -/
def joint (s : Fin n → U → V) (x : U) : Fin n → V := fun j => s j x

/-- §1.1 的不可约性：存在分离见证 `(x, y)` -/
def irreducible (s : Fin n → U → V) (i : Fin n) : Prop :=
  ∃ x y : U, (∀ j, j ≠ i → s j x = s j y) ∧ s i x ≠ s i y

/-- §1.1 的共同覆盖：每个 `q ∈ Q` 都有解码 `c_q` 使 `q = c_q ∘ F_S` -/
def covers (s : Fin n → U → V) (Q : Set (U → W)) : Prop :=
  ∀ q ∈ Q, ∃ c : (Fin n → V) → W, q = c ∘ joint s

/-- 裸基：每个面都有不可约见证且共同覆盖 `Q`；不附加 `n = 4` -/
def staticBase (s : Fin n → U → V) (Q : Set (U → W)) : Prop :=
  (∀ i, irreducible s i) ∧ covers s Q

/-- `(U, Q)` 上的静态四维基 -/
def staticBase4 (s : Fin 4 → U → V) (Q : Set (U → W)) : Prop := staticBase s Q

end StaticBase

/-! ### 具体例子：`U = Bool × Bool`，`n = 2` -/
section Examples

/-- 两个投影：`s_0 = fst`，`s_1 = snd` -/
def ex2 : Fin 2 → Bool × Bool → Bool
  | 0 => Prod.fst
  | 1 => Prod.snd

/-- fst 相对 (fst, snd) 不可约；见证为 (true,false) 与 (false,false) -/
theorem ex2_irreducible_0 : irreducible ex2 0 := by unfold irreducible; decide
theorem ex2_irreducible_1 : irreducible ex2 1 := by unfold irreducible; decide

/-- 两个面都取 fst：`s_0` 可由 `s_1` 重建（`r_0 = id`），所以不存在分离见证 —— decide -/
def ex2dup : Fin 2 → Bool × Bool → Bool
  | 0 => Prod.fst
  | 1 => Prod.fst

theorem ex2dup_not_irreducible : ¬ irreducible ex2dup 0 := by unfold irreducible; decide

/-- §1.1 可约性的正面形式：给出重建函数 `r_0` 并在整个 `U` 上验证 -/
theorem ex2dup_reducible : ∃ r : Bool → Bool, ∀ x, ex2dup 0 x = r (ex2dup 1 x) :=
  ⟨id, fun _ => rfl⟩

/-- 覆盖例：`q = fst ∧ snd` 由联合观察经解码 `c v = v 0 ∧ v 1` 得到 -/
theorem ex2_covers_and : covers ex2 {fun p => p.1 && p.2} := by
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  exact ⟨fun v => v 0 && v 1, rfl⟩

/-- 不覆盖例：`(fst, fst)` 覆盖不了 `snd` —— 联合观察在 (true,true)/(true,false) 上相同而 snd 不同 -/
theorem ex2dup_not_covers_snd : ¬ covers ex2dup {Prod.snd} := by
  intro h
  obtain ⟨c, hc⟩ := h Prod.snd rfl
  have h1 := congrFun hc (true, true)
  have h2 := congrFun hc (true, false)
  have hj : joint ex2dup (true, true) = joint ex2dup (true, false) := by decide
  simp only [Function.comp_apply] at h1 h2
  rw [hj] at h1
  exact absurd (h1.trans h2.symm) (by decide)

/-- 两个面都不可约（一次 decide） -/
theorem ex2_all_irreducible : ∀ i, irreducible ex2 i := by unfold irreducible; decide

/-- 例子确实是 `(U, Q)` 上的（二维）裸基 -/
theorem ex2_staticBase : staticBase ex2 {fun p => p.1 && p.2} :=
  ⟨ex2_all_irreducible, ex2_covers_and⟩

end Examples

/-! ## 命题 1（独立标签置换不变性）
文档是元陈述「只由裸基定义推出的命题在 Sym(S) 下不变」。这里逐谓词落实：
`irreducible`、`covers`、`staticBase` 在重排 `s ∘ π` 下真假不变，一般 `n`。
动态基 Sym(D) 那一半未定义（本批不含 §1.2 动态基）。-/
section Perm
variable {U V W : Type*} {n : ℕ}

/-- 重排后第 `j` 面不可约 ⇔ 原来第 `π j` 面不可约 -/
theorem irreducible_reindex (s : Fin n → U → V) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    irreducible (s ∘ π) j ↔ irreducible s (π j) := by
  unfold irreducible
  constructor
  · rintro ⟨x, y, h1, h2⟩
    refine ⟨x, y, fun k hk => ?_, h2⟩
    have := h1 (π.symm k) (fun h => hk (by rw [← h, Equiv.apply_symm_apply]))
    simpa using this
  · rintro ⟨x, y, h1, h2⟩
    exact ⟨x, y, fun k hk => h1 (π k) (fun h => hk (π.injective h)), h2⟩

/-- 任务给的形状：`irreducible (s ∘ π) (π⁻¹ i) ↔ irreducible s i` -/
theorem irreducible_reindex_symm (s : Fin n → U → V) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    irreducible (s ∘ π) (π.symm i) ↔ irreducible s i := by
  rw [irreducible_reindex, Equiv.apply_symm_apply]

/-- 解码器随重排搬家：`c' v = c (v ∘ π⁻¹)` -/
theorem covers_reindex_of (s : Fin n → U → V) (π : Equiv.Perm (Fin n)) (Q : Set (U → W))
    (h : covers s Q) : covers (s ∘ π) Q := by
  intro q hq
  obtain ⟨c, hc⟩ := h q hq
  refine ⟨fun v => c (v ∘ π.symm), ?_⟩
  subst hc
  funext x
  simp only [Function.comp_apply]
  congr 1
  funext j
  simp [joint]

theorem covers_reindex (s : Fin n → U → V) (π : Equiv.Perm (Fin n)) (Q : Set (U → W)) :
    covers (s ∘ π) Q ↔ covers s Q := by
  constructor
  · intro h
    have := covers_reindex_of (s ∘ π) π.symm Q h
    rwa [show (s ∘ π) ∘ π.symm = s from by funext j; simp] at this
  · exact covers_reindex_of s π Q

/-- 命题 1（静态半边）：裸基性质在 `Sym(S)` 下不变 -/
theorem staticBase_reindex (s : Fin n → U → V) (π : Equiv.Perm (Fin n)) (Q : Set (U → W)) :
    staticBase (s ∘ π) Q ↔ staticBase s Q := by
  unfold staticBase
  rw [covers_reindex]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    have := h1 (π.symm i)
    rwa [irreducible_reindex, Equiv.apply_symm_apply] at this
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (irreducible_reindex s π i).2 (h1 _), h2⟩

end Perm

/-! ## §2.1 静态布尔闭包 -/

/-- `|B_n| = 2^n`，一般 `n` -/
theorem B_card (n : ℕ) : Fintype.card (Finset (Fin n)) = 2 ^ n := by
  rw [Fintype.card_finset, Fintype.card_fin]

/-- 第 `k` 秩有 `C(n,k)` 个元素 -/
theorem B_rank (n k : ℕ) :
    (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card = n.choose k := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- §2.1 表的总数列：2, 4, 8, 16 -/
theorem B_table :
    Fintype.card (Finset (Fin 1)) = 2 ∧ Fintype.card (Finset (Fin 2)) = 4 ∧
    Fintype.card (Finset (Fin 3)) = 8 ∧ Fintype.card (Finset (Fin 4)) = 16 := by
  simp only [B_card]; decide

/-- §2.1 表的秩向量：(1,1) (1,2,1) (1,3,3,1) (1,4,6,4,1) -/
theorem B_rank_table :
    (Nat.choose 1 0, Nat.choose 1 1) = (1, 1) ∧
    (Nat.choose 2 0, Nat.choose 2 1, Nat.choose 2 2) = (1, 2, 1) ∧
    (Nat.choose 3 0, Nat.choose 3 1, Nat.choose 3 2, Nat.choose 3 3) = (1, 3, 3, 1) ∧
    (Nat.choose 4 0, Nat.choose 4 1, Nat.choose 4 2, Nat.choose 4 3, Nat.choose 4 4)
      = (1, 4, 6, 4, 1) := by
  decide

/-! ## §2.2 动态有限规范形 -/

/-- `|W_n(k)| = P(n,k)`；互异有序词由单射 `Fin k ↪ Fin n` 表示 -/
theorem W_rank (n k : ℕ) : Fintype.card (Fin k ↪ Fin n) = n.descFactorial k := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- `|W_n| = Σ_{k=1}^n P(n,k)` -/
def Wcard (n : ℕ) : ℕ := ((List.range n).map fun k => n.descFactorial (k + 1)).sum

/-- §2.2 表的总数列：1, 4, 15, 64 -/
theorem W_table : Wcard 1 = 1 ∧ Wcard 2 = 4 ∧ Wcard 3 = 15 ∧ Wcard 4 = 64 := by decide

/-- §2.2 表的长度向量：(1) (2,2) (3,6,6) (4,12,24,24)，以嵌入基数陈述 -/
theorem W_len_table :
    Fintype.card (Fin 1 ↪ Fin 1) = 1 ∧
    (Fintype.card (Fin 1 ↪ Fin 2), Fintype.card (Fin 2 ↪ Fin 2)) = (2, 2) ∧
    (Fintype.card (Fin 1 ↪ Fin 3), Fintype.card (Fin 2 ↪ Fin 3), Fintype.card (Fin 3 ↪ Fin 3))
      = (3, 6, 6) ∧
    (Fintype.card (Fin 1 ↪ Fin 4), Fintype.card (Fin 2 ↪ Fin 4), Fintype.card (Fin 3 ↪ Fin 4),
      Fintype.card (Fin 4 ↪ Fin 4)) = (4, 12, 24, 24) := by
  simp only [W_rank]; decide

/-- `Wcard` 与嵌入基数之和一致（n = 4） -/
theorem W4_sum :
    Fintype.card (Fin 1 ↪ Fin 4) + Fintype.card (Fin 2 ↪ Fin 4) + Fintype.card (Fin 3 ↪ Fin 4)
      + Fintype.card (Fin 4 ↪ Fin 4) = Wcard 4 := by
  simp only [W_rank]; decide

/-! ## 命题 4（历史长度无统一有限上界） -/
section History

/-- §3.2 的顺序历史：事件 = (独立身份, 方向标签)；方向标签可以重复 -/
abbrev Event := ℕ × Lens64.Sym
abbrev History := List Event

/-- 事件身份互异 -/
def History.valid (H : History) : Prop := (H.map Prod.fst).Nodup

/-- 命题 4 的构造：`H_m` = `m` 个不同身份、标签均为 `d` 的历史；取 `m = N + 1` -/
theorem history_unbounded (d : Lens64.Sym) (N : ℕ) :
    ∃ H : History, H.valid ∧ (∀ e ∈ H, e.2 = d) ∧ N < H.length := by
  refine ⟨(List.range (N + 1)).map fun k => (k, d), ?_, ?_, ?_⟩
  · simp [History.valid, Function.comp_def, List.nodup_range]
  · simp
  · simp

/-- 命题 4 的陈述形状：不存在统一上界 `N` -/
theorem no_uniform_bound (d : Lens64.Sym) :
    ¬ ∃ N, ∀ H : History, H.valid → (∀ e ∈ H, e.2 = d) → H.length ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨H, h1, h2, h3⟩ := history_unbounded d N
  have := hN H h1 h2
  omega

end History

/-! ## 命题 5（栈解析的条件唯一性）
标签 S D R I ↦ 0 1 2 3（`Lens64.Sym = Fin 4`）。配对 `(i, j)`：位置 `i` 打开、位置 `j` 恢复，
两端标签相同（回到根）。良构 = 任意两个闭区间不交或一者严格包含另一者。-/
section Parse
open Lens64

/-- §3.3 的标签串例 `SDRDIR` -/
def sdrdir : List Sym := [0, 1, 2, 1, 3, 2]

/-- 单个配对合法：`i < j < |w|`，`w_i = w_j` -/
def pairOk (w : List Sym) (q : ℕ × ℕ) : Bool :=
  q.1 < q.2 && q.2 < w.length && w.getD q.1 0 == w.getD q.2 0

/-- 两个闭区间不交，或一者严格包含另一者 -/
def nestOk (a b : ℕ × ℕ) : Bool :=
  a.2 < b.1 || b.2 < a.1 || (a.1 < b.1 && b.2 < a.2) || (b.1 < a.1 && a.2 < b.2)

def pairwiseNest : List (ℕ × ℕ) → Bool
  | [] => true
  | a :: rest => rest.all (nestOk a) && pairwiseNest rest

/-- §3.3 的良构配对 -/
def wellFormed (w : List Sym) (p : List (ℕ × ℕ)) : Bool :=
  p.all (pairOk w) && pairwiseNest p

/-- 嵌套树的线性显示：打开 / 恢复 / 普通事件 -/
inductive Tok
  | op (s : Sym)
  | cl (s : Sym)
  | ev (s : Sym)
  deriving DecidableEq, Repr

/-- §3.3 的栈解析：按事件顺序压栈，恢复点只能关闭当前最内层打开点；
栈存各打开点的恢复位置。恢复点与栈顶不匹配（配对不良构）→ `none`。 -/
def parseAux (p : List (ℕ × ℕ)) : ℕ → List Sym → List ℕ → List Tok → Option (List Tok)
  | _, [], [], out => some out.reverse
  | _, [], _ :: _, _ => none
  | k, c :: rest, st, out =>
    match p.find? (fun q => q.1 == k) with
    | some q => parseAux p (k + 1) rest (q.2 :: st) (Tok.op c :: out)
    | none =>
      match p.find? (fun q => q.2 == k), st with
      | some _, j :: st' =>
        if j == k then parseAux p (k + 1) rest st' (Tok.cl c :: out) else none
      | some _, [] => none
      | none, _ => parseAux p (k + 1) rest st (Tok.ev c :: out)

def parse (w : List Sym) (p : List (ℕ × ℕ)) : Option (List Tok) := parseAux p 0 w [] []

/-- (a) 给定配对下解析唯一：`parse` 是函数，唯一性即函数性 -/
theorem parse_det (w : List Sym) (p : List (ℕ × ℕ)) {t₁ t₂ : List Tok}
    (h₁ : parse w p = some t₁) (h₂ : parse w p = some t₂) : t₁ = t₂ :=
  Option.some.inj (h₁.symm.trans h₂)

/-- 候选配对一：`DRD`（位置 1–3） -/
def pDRD : List (ℕ × ℕ) := [(1, 3)]
/-- 候选配对二：`RDIR`（位置 2–5） -/
def pRDIR : List (ℕ × ℕ) := [(2, 5)]

/-- (b) 两个配对都良构、互不相同，解析结果也不同 -/
theorem both_wellFormed : wellFormed sdrdir pDRD = true ∧ wellFormed sdrdir pRDIR = true := by
  decide
theorem pairings_differ : pDRD ≠ pRDIR := by decide
theorem parses_differ : parse sdrdir pDRD ≠ parse sdrdir pRDIR := by decide
theorem parse_DRD :
    parse sdrdir pDRD = some [Tok.ev 0, Tok.op 1, Tok.ev 2, Tok.cl 1, Tok.ev 3, Tok.ev 2] := by
  decide
theorem parse_RDIR :
    parse sdrdir pRDIR = some [Tok.ev 0, Tok.ev 1, Tok.op 2, Tok.ev 1, Tok.ev 3, Tok.cl 2] := by
  decide

/-- 两个候选同时取则交叉，不良构；标签本身不决定哪个区间承担返回关系 -/
theorem crossing_not_wellFormed : wellFormed sdrdir (pDRD ++ pRDIR) = false := by decide

/-- 交叉配对下栈解析失败（位置 3 要关 D，栈顶却是 R 的恢复位置 5）；良构是解析的前提 -/
theorem parse_crossing_none : parse sdrdir (pDRD ++ pRDIR) = none := by decide

/-- 该串的合法配对只有这两个（同标签位置对只有 (1,3) 与 (2,5)） -/
theorem only_two_pairs :
    ∀ i < 6, ∀ j < 6, pairOk sdrdir (i, j) = true → (i, j) = (1, 3) ∨ (i, j) = (2, 5) := by
  decide

/-- (c) 具体例验证：固定「最近匹配」规则（`Lens64.loopErase`）后，`SDRDIR`
分解为 `DRD`，残余 `S D I R`。这不证明该规则对任意输入的一般正确性。 -/
theorem nearest_match_unique : loopErase sdrdir = ([[1, 2, 1]], [0, 1, 3, 2]) := by decide

end Parse

/-! ## 定理 2（布尔闭包的乘积分解）
不交并 `E ⊔ F` 用和类型 `α ⊕ β`；`P(·)` 用 `Finset`。
mathlib 现成：`Finset.sumEquiv : Finset (α ⊕ β) ≃o Finset α × Finset β`（Data/Finset/Sum.lean），
其正向即 `φ(I) = (I ∩ E, I ∩ F)`（`toLeft`/`toRight`），逆向即 `ψ(U,V) = U ∪ V`（`disjSum`）。
这里按文档的 `φ`/`ψ` 显式写出，互逆与保持各运算都引 mathlib 引理。-/
section Product
variable {α β : Type*}

/-- `φ(I) = (I ∩ E_m, I ∩ F_n)` -/
def phi (I : Finset (α ⊕ β)) : Finset α × Finset β := (I.toLeft, I.toRight)
/-- `ψ(U, V) = U ∪ V` -/
def psi (p : Finset α × Finset β) : Finset (α ⊕ β) := p.1.disjSum p.2

theorem psi_phi (I : Finset (α ⊕ β)) : psi (phi I) = I := Finset.toLeft_disjSum_toRight
theorem phi_psi (p : Finset α × Finset β) : phi (psi p) = p := by simp [phi, psi]

/-- 定理 2 的双射 -/
def powersetSumEquiv : Finset (α ⊕ β) ≃ Finset α × Finset β :=
  ⟨phi, psi, psi_phi, phi_psi⟩

/-- 与 mathlib 的 `Finset.sumEquiv` 逐点一致 -/
theorem powersetSumEquiv_eq_sumEquiv (I : Finset (α ⊕ β)) :
    powersetSumEquiv I = Finset.sumEquiv I := rfl

/-- 保持包含 -/
theorem phi_subset (I J : Finset (α ⊕ β)) :
    I ⊆ J ↔ (phi I).1 ⊆ (phi J).1 ∧ (phi I).2 ⊆ (phi J).2 := by
  constructor
  · intro h
    exact ⟨Finset.toLeft_subset_toLeft h, Finset.toRight_subset_toRight h⟩
  · rintro ⟨h1, h2⟩
    rw [← psi_phi I]
    exact Finset.disjSum_subset.2 ⟨h1, h2⟩

variable [DecidableEq α] [DecidableEq β]

/-- 保持交 -/
theorem phi_inter (I J : Finset (α ⊕ β)) :
    phi (I ∩ J) = ((phi I).1 ∩ (phi J).1, (phi I).2 ∩ (phi J).2) := by
  simp [phi, Finset.toLeft_inter, Finset.toRight_inter]

/-- 保持并 -/
theorem phi_union (I J : Finset (α ⊕ β)) :
    phi (I ∪ J) = ((phi I).1 ∪ (phi J).1, (phi I).2 ∪ (phi J).2) := by
  simp [phi, Finset.toLeft_union, Finset.toRight_union]

end Product

section ProductBounds
variable {α β : Type*}

/-- 保持空元 -/
theorem phi_empty : phi (∅ : Finset (α ⊕ β)) = (∅, ∅) := by
  simp only [phi, Prod.mk.injEq]
  constructor <;> ext x <;> simp

variable [Fintype α] [Fintype β]

/-- 保持全集 -/
theorem phi_univ : phi (Finset.univ : Finset (α ⊕ β)) = (Finset.univ, Finset.univ) := by
  simp [phi]

variable [DecidableEq α] [DecidableEq β]

/-- 保持补 -/
theorem phi_compl (I : Finset (α ⊕ β)) : phi Iᶜ = ((phi I).1ᶜ, (phi I).2ᶜ) := by
  simp [phi, Finset.compl_eq_univ_sdiff, Finset.toLeft_sdiff, Finset.toRight_sdiff]

end ProductBounds

/-- `Finset` 沿类型等价搬运（mathlib 无现成 `Equiv.finsetCongr`，自写） -/
def finsetMapEquiv {α β : Type*} (e : α ≃ β) : Finset α ≃ Finset β where
  toFun s := s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by ext x; simp [Finset.mem_map_equiv]
  right_inv s := by ext x; simp [Finset.mem_map_equiv]

/-- 定理 2 在 `Fin` 上的形状：`P(E_{m+n}) ≅ P(E_m) × P(F_n)` -/
def finPowersetProd (m n : ℕ) : Finset (Fin (m + n)) ≃ Finset (Fin m) × Finset (Fin n) :=
  (finsetMapEquiv finSumFinEquiv.symm).trans powersetSumEquiv

/-- 基数对应：`2^{m+n} = 2^m · 2^n` -/
theorem B_card_add (m n : ℕ) :
    Fintype.card (Finset (Fin (m + n))) =
      Fintype.card (Finset (Fin m)) * Fintype.card (Finset (Fin n)) := by
  simp only [B_card, pow_add]

/-- §4.3 分区递归的一例：`B_9 ≅ B_4 × B_4 × B_1`，其中 q = 2, r = 1 -/
def B9_decomp : Finset (Fin 9) ≃ (Finset (Fin 4) × Finset (Fin 4)) × Finset (Fin 1) :=
  (finPowersetProd 8 1).trans ((finPowersetProd 4 4).prodCongr (Equiv.refl _))

/-! ## §4.3 动态词不是局部投影词对
交错记录 `σ` 让全局词严格多于两个局部投影词本身。-/

/-- 文档要求的两例：m = n = 1（4 ≠ 1）与 m = n = 2（64 ≠ 16） -/
theorem W_not_product_examples :
    Wcard (1 + 1) ≠ Wcard 1 * Wcard 1 ∧ Wcard (2 + 2) ≠ Wcard 2 * Wcard 2 := by decide

/-- 1 ≤ m, n ≤ 4 全表：全局词严格多于局部词对 -/
theorem W_gt_product_small :
    ∀ m < 5, ∀ n < 5, 1 ≤ m → 1 ≤ n → Wcard m * Wcard n < Wcard (m + n) := by decide

/-- 正文含空词公式的三个直接有限反例：
`W_(m+n) ≠ (W_m^ε × W_n^ε) \ {(ε, ε)}`。右侧基数为
`(Wcard m + 1) * (Wcard n + 1) - 1`。 -/
theorem W_not_epsilon_product_examples :
    Wcard (1 + 1) ≠ (Wcard 1 + 1) * (Wcard 1 + 1) - 1 ∧
    Wcard (1 + 2) ≠ (Wcard 1 + 1) * (Wcard 2 + 1) - 1 ∧
    Wcard (2 + 2) ≠ (Wcard 2 + 1) * (Wcard 2 + 1) - 1 := by decide

/-! ## 命题 6（拓扑排序不产生唯一因果顺序）
mathlib 有 Szpilrajn：`extend_partialOrder`（Order/Extension/Linear.lean，Zorn）。
文档证明「对不可比元素分别加入 a≺b 与 b≺a 均不成环」= 下面的 `addPair` 仍是偏序。-/
section Topo
variable {α : Type*}

/-- 把 `a ≺ b` 加进偏序 `r`（传递闭包一步到位）：`x ≤ y ∨ (x ≤ a ∧ b ≤ y)` -/
def addPair (r : α → α → Prop) (a b : α) : α → α → Prop :=
  fun x y => r x y ∨ (r x a ∧ r b y)

/-- 「加入 a≺b 不成环」：`¬ r b a` 时 `addPair r a b` 仍是偏序 -/
theorem addPair_isPartialOrder (r : α → α → Prop) [IsPartialOrder α r] (a b : α)
    (hba : ¬ r b a) : IsPartialOrder α (addPair r a b) where
  refl x := Or.inl (refl x)
  trans x y z hxy hyz := by
    rcases hxy with h1 | ⟨h1, h2⟩ <;> rcases hyz with h3 | ⟨h3, h4⟩
    · exact Or.inl (_root_.trans h1 h3)
    · exact Or.inr ⟨_root_.trans h1 h3, h4⟩
    · exact Or.inr ⟨h1, _root_.trans h2 h3⟩
    · exact Or.inr ⟨h1, h4⟩
  antisymm x y hxy hyx := by
    rcases hxy with h1 | ⟨h1, h2⟩ <;> rcases hyx with h3 | ⟨h3, h4⟩
    · exact antisymm h1 h3
    · exact absurd (_root_.trans h4 (_root_.trans h1 h3)) hba
    · exact absurd (_root_.trans h2 (_root_.trans h3 h1)) hba
    · exact absurd (_root_.trans h2 h3) hba

/-- 存在线性扩展把 `a` 排在 `b` 前（Szpilrajn 用在 `addPair` 上） -/
theorem exists_linear_ext_with (r : α → α → Prop) [IsPartialOrder α r] (a b : α)
    (hba : ¬ r b a) : ∃ s : α → α → Prop, IsLinearOrder α s ∧ r ≤ s ∧ s a b := by
  have := addPair_isPartialOrder r a b hba
  obtain ⟨s, hs, hle⟩ := extend_partialOrder (addPair r a b)
  exact ⟨s, hs, fun x y h => hle x y (Or.inl h), hle a b (Or.inr ⟨refl a, refl b⟩)⟩

/-- 命题 6：`a, b` 不可比 ⇒ 存在两个线性扩展，二者次序相反 -/
theorem two_linear_extensions (r : α → α → Prop) [IsPartialOrder α r] (a b : α)
    (hab : ¬ r a b) (hba : ¬ r b a) :
    ∃ s t : α → α → Prop, IsLinearOrder α s ∧ IsLinearOrder α t ∧ r ≤ s ∧ r ≤ t ∧
      (s a b ∧ ¬ s b a) ∧ (t b a ∧ ¬ t a b) := by
  obtain ⟨s, hs, hrs, hsab⟩ := exists_linear_ext_with r a b hba
  obtain ⟨t, ht, hrt, htba⟩ := exists_linear_ext_with r b a hab
  have hne : a ≠ b := fun h => hab (h ▸ refl a)
  refine ⟨s, t, hs, ht, hrs, hrt, ⟨hsab, fun h => hne ?_⟩, ⟨htba, fun h => hne ?_⟩⟩
  · have := hs; exact antisymm hsab h
  · have := ht; exact antisymm h htba

/-! ### 具体见证（decide）：`Fin 4` 上偏序 `0,1 ≺ 2,3`，`0` 与 `1` 不可比 -/

/-- 偏序（含自反）：`x = y ∨ (x ∈ {0,1} ∧ y ∈ {2,3})` -/
def r4 (x y : Fin 4) : Bool := x == y || ((x == 0 || x == 1) && (y == 2 || y == 3))

theorem r4_partialOrder :
    (∀ x, r4 x x = true) ∧ (∀ x y z, r4 x y = true → r4 y z = true → r4 x z = true) ∧
    (∀ x y, r4 x y = true → r4 y x = true → x = y) := by decide

theorem r4_incomparable : r4 0 1 = false ∧ r4 1 0 = false := by decide

/-- 列表 `L` 是 `r4` 的一个拓扑排序：无重、全 4 元、保持 `r4` -/
def topoSort (L : List (Fin 4)) : Prop :=
  L.Nodup ∧ L.length = 4 ∧ ∀ x y, r4 x y = true → L.idxOf x ≤ L.idxOf y

/-- 两个拓扑排序，`0`/`1` 次序相反 -/
theorem topo_two :
    topoSort [0, 1, 2, 3] ∧ topoSort [1, 0, 2, 3] ∧
    ([0, 1, 2, 3] : List (Fin 4)).idxOf 0 < ([0, 1, 2, 3] : List (Fin 4)).idxOf 1 ∧
    ([1, 0, 2, 3] : List (Fin 4)).idxOf 1 < ([1, 0, 2, 3] : List (Fin 4)).idxOf 0 := by
  unfold topoSort; decide

end Topo

end K4Article
