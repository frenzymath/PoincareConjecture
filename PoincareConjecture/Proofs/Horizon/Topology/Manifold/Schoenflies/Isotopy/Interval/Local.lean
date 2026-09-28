import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem exists_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
    {a b l u : Real} {U : Set E2} (hU : IsOpen U)
    (f : Real × Real -> E2) {W : Set (Real × Real)}
    (hW : IsOpen W) (hrect : Icc a b ×ˢ Icc l u ⊆ W)
    (hf : ContDiffOn Real ∞ f W)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (htrace : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, f (t, s) ∈ U) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ U ∧
      ∃ Phi : Real -> Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
      (∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, Phi t (f (a, s)) = f (t, s) := by
  obtain ⟨F, V, hF, hV, hKV, _, hFeq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact
      (isCompact_Icc.prod isCompact_Icc) hW hrect f hf
  have heq (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      F (t, s) = f (t, s) := hFeq (hKV ⟨ht, hs⟩)
  have hFder (t : Real) (ht : t ∈ Icc a b) (s : Real) (hs : s ∈ Icc l u) :
      deriv (fun y => F (t, y)) s = deriv (fun y => f (t, y)) s := by
    apply Filter.EventuallyEq.deriv_eq
    have hnear : ∀ᶠ y in 𝓝 s, (t, y) ∈ V :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (hV.mem_nhds (hKV ⟨ht, hs⟩))
    exact hnear.mono (fun _ hy => hFeq hy)
  obtain ⟨K, hK, hKU, Phi, hi, hs, hfix, hmotion⟩ :=
    exists_ambient_isotopy_of_interval_isotopy_within hU F hF (by
      intro t ht s hsl v hvl he
      apply hinj t ht hsl hvl
      simpa only [heq t ht s hsl, heq t ht v hvl] using he) (by
      intro t ht s hs
      rw [hFder t ht s hs]
      exact hder t ht s hs) (by
      intro t ht s hs
      rw [heq t ht s hs]
      exact htrace t ht s hs)
  refine ⟨K, hK, hKU, Phi, hi, hs, hfix, fun t ht s hs => ?_⟩
  simpa only [heq a ⟨le_rfl, ht.1.trans ht.2⟩ s hs, heq t ht s hs] using
    hmotion t ht s hs

end Poincare.Manifold.Schoenflies
