import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

open Set Topology

namespace IsLocallyInjective

theorem comp {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {p : B → C} {q : A → B} (hp : IsLocallyInjective p) (hq : IsLocallyInjective q)
    (hcont : Continuous q) : IsLocallyInjective (p ∘ q) := by
  intro x
  obtain ⟨U, hU, hxU, hinjU⟩ := hp (q x)
  obtain ⟨W, hW, hxW, hinjW⟩ := hq x
  refine ⟨W ∩ q ⁻¹' U, hW.inter (hU.preimage hcont), ⟨hxW, hxU⟩, ?_⟩
  intro a ha b hb heq
  exact hinjW ha.1 hb.1 (hinjU ha.2 hb.2 heq)

theorem exists_factorization_of_preconnected_fibers
    {A B E X : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace E] [T2Space E]
    {p : E → X} (hp : IsLocallyInjective p)
    (a : C(A, B)) (ha : IsQuotientMap a)
    (hfiber : ∀ b, IsPreconnected (a ⁻¹' {b}))
    (q : B → X) (g : C(A, E)) (hg : ∀ u, p (g u) = q (a u)) :
    ∃ k : C(B, E), (∀ v, p (k v) = q v) ∧
      (∀ u, k (a u) = g u) ∧ range k = range g := by
  classical
  choose r hr using ha.surjective
  have hconst {u v : A} (huv : a u = a v) : g u = g v := by
    apply (T2Space.isSeparatedMap p).constOn_of_comp hp (hfiber (a u))
      g.continuous.continuousOn _ (show u ∈ a ⁻¹' {a u} from rfl)
      (show v ∈ a ⁻¹' {a u} from huv.symm)
    intro x hx y hy
    change a x = a u at hx
    change a y = a u at hy
    exact (hg x).trans ((congrArg q (hx.trans hy.symm)).trans (hg y).symm)
  let kfun : B → E := fun b => g (r b)
  have hkg (u : A) : kfun (a u) = g u := hconst (hr (a u))
  have hkcont : Continuous kfun := ha.continuous_iff.mpr
    (g.continuous.congr (fun u => (hkg u).symm))
  let k : C(B, E) := ⟨kfun, hkcont⟩
  refine ⟨k, fun v => (hg (r v)).trans (congrArg q (hr v)), hkg, ?_⟩
  ext e
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := ha.surjective v
    exact ⟨u, (hkg u).symm.trans (congrArg k hu)⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a u, hkg u⟩

end IsLocallyInjective
