/-!
# 圈弹出分解（最小测试）
永杰 2026-09-11：「以循环回到原点为一个动态状态」。例 aabacbcdacad → aa, aba, cbc, acda, aca + 残余 ad。
字母表用 `Fin 4`（a b c d ↦ 0 1 2 3；T C R X ↦ 0 1 2 3），kernel 可归约。
本文件只做最小验证：定义分解函数，用 `decide` 核具体例子的输出等于手写结果。不证一般性质。
-/
namespace Lens64

abbrev Sym := Fin 4

/-- 一步：栈 = 当前无重复开路径（按进入顺序）。读到 c：若 c 在栈中，从 c 到栈顶闭成圈（c…c），栈退回到 c；否则压栈 -/
def step (st : List Sym × List (List Sym)) (c : Sym) : List Sym × List (List Sym) :=
  let (stack, cycles) := st
  match stack.findIdx? (· == c) with
  | some i => (stack.take (i + 1), cycles ++ [stack.drop i ++ [c]])
  | none => (stack ++ [c], cycles)

/-- 圈弹出：返回 (圈列表, 残余开路径) -/
def loopErase (w : List Sym) : List (List Sym) × List Sym :=
  let (stack, cycles) := w.foldl step ([], [])
  (cycles, stack)

/-- a a b a c b c d a c a d -/
def yongjieExample : List Sym := [0, 0, 1, 0, 2, 1, 2, 3, 0, 2, 0, 3]

/-- 永杰手写的分解：aa, aba, cbc, acda, aca；残余 ad -/
theorem yongjie_decomposition :
    loopErase yongjieExample =
      ([[0, 0], [0, 1, 0], [2, 1, 2], [0, 2, 3, 0], [0, 2, 0]], [0, 3]) := by decide

/-- 圈的阶 = 不同符号数 = 长度 − 1 -/
theorem yongjie_orders :
    ((loopErase yongjieExample).1.map fun c => c.length - 1) = [1, 2, 2, 3, 2] := by decide

/-- 澄序 √p 证明序列 X T C R T C T T C T T C R X（T C R X ↦ 0 1 2 3） -/
theorem chengxu_sqrt_p :
    loopErase [3, 0, 1, 2, 0, 1, 0, 0, 1, 0, 0, 1, 2, 3] =
      ([[0, 1, 2, 0], [0, 1, 0], [0, 0], [0, 1, 0], [0, 0], [3, 0, 1, 2, 3]], [3]) := by decide

/-- 流水线 TCRX×3：两个四阶圈 + 残余 TCRX -/
theorem pipeline :
    loopErase [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3] =
      ([[0, 1, 2, 3, 0], [0, 1, 2, 3, 0]], [0, 1, 2, 3]) := by decide


end Lens64
