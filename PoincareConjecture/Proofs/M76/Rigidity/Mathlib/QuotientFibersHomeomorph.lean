import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false

namespace Topology.IsQuotientMap

variable {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X]
  [TopologicalSpace Y] {q : C(S, X)} {r : C(S, Y)}

theorem exists_homeomorph_of_fibers (hq : IsQuotientMap q)
    (hr : IsQuotientMap r)
    (hfib : ∀ a b : S, q a = q b ↔ r a = r b) :
    ∃ g : X ≃ₜ Y, ∀ a : S, g (q a) = r a := by
  let hf : Function.FactorsThrough r q := fun a b h => (hfib a b).mp h
  let hb : Function.FactorsThrough q r := fun a b h => (hfib a b).mpr h
  let f : C(X, Y) := hq.lift r hf
  let b : C(Y, X) := hr.lift q hb
  have hfq (a : S) : f (q a) = r a := by
    exact congrArg (fun k : C(S, Y) => k a) (hq.lift_comp r hf)
  have hbr (a : S) : b (r a) = q a := by
    exact congrArg (fun k : C(S, X) => k a) (hr.lift_comp q hb)
  refine ⟨{
    toFun := f
    invFun := b
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := f.continuous
    continuous_invFun := b.continuous }, hfq⟩
  · intro x
    obtain ⟨a, rfl⟩ := hq.surjective x
    rw [hfq, hbr]
  · intro y
    obtain ⟨a, rfl⟩ := hr.surjective y
    rw [hbr, hfq]

end Topology.IsQuotientMap
