import PoincareConjecture.Proofs.M47.TerminalCommonIntervalGlueRows









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u v

namespace PoincareConjecture.M47



theorem terminalCommonInterval_limit_left_inverse
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N]
    {T : ℕ → M → N} {S : ℕ → N → M} (t : M → N) (s : N → M)
    (hcomp : ∀ x, Tendsto (fun n => S n (T n x)) atTop (𝓝 (s (t x))))
    (hid : ∀ x, ∀ᶠ n in atTop, S n (T n x) = x) :
    Function.LeftInverse s t := by
  intro x
  exact tendsto_nhds_unique (hcomp x)
    (Filter.Tendsto.congr' (Filter.EventuallyEq.symm (hid x)) tendsto_const_nhds)



theorem terminalCommonInterval_limit_right_inverse
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N]
    {T : ℕ → M → N} {S : ℕ → N → M} (t : M → N) (s : N → M)
    (hcomp : ∀ y, Tendsto (fun n => T n (S n y)) atTop (𝓝 (t (s y))))
    (hid : ∀ y, ∀ᶠ n in atTop, T n (S n y) = y) :
    Function.RightInverse s t := by
  intro y
  exact tendsto_nhds_unique (hcomp y)
    (Filter.Tendsto.congr' (Filter.EventuallyEq.symm (hid y)) tendsto_const_nhds)

end PoincareConjecture.M47
