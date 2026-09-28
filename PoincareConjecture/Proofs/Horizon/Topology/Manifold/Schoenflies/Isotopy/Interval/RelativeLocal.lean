import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.Relative



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)



theorem exists_relative_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
    {a b l l₀ l₁ u₁ u₀ u : Real} (hab : a < b)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    {U : Set E2} (hU : IsOpen U)
    (f : Real × Real → E2) {W : Set (Real × Real)}
    (hW : IsOpen W) (hrect : Icc a b ×ˢ Icc l u ⊆ W)
    (hf : ContDiffOn Real ∞ f W)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => f (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0)
    (hstationary : ∀ t ∈ Icc a b, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u,
      f (t, s) = f (a, s))
    (htrace : ∀ t ∈ Icc a b, ∀ s ∈ Icc l₁ u₁, f (t, s) ∈ U) :
    ∃ K O : Set E2, IsCompact K ∧ K ⊆ U ∧ IsOpen O ∧
      (fun s => f (a, s)) '' (Icc l l₀ ∪ Icc u₀ u) ⊆ O ∧ Disjoint K O ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        (∀ t x, x ∈ O → Phi t x = x) ∧
        ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, Phi t (f (a, s)) = f (t, s) := by
  have hmid : Icc l₁ u₁ ⊆ Icc l u :=
    Icc_subset_Icc (hll₀.trans hl₀l₁.le) (hu₁u₀.le.trans hu₀u)
  have hend : Icc l l₁ ∪ Icc u₁ u ⊆ Icc l u := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨hs.1, hs.2.trans (hl₁u₁.trans (hu₁u₀.le.trans hu₀u))⟩
    · exact ⟨(hll₀.trans (hl₀l₁.le.trans hl₁u₁)).trans hs.1, hs.2⟩
  have hendSmall : Icc l l₀ ∪ Icc u₀ u ⊆ Icc l u := by
    intro s hs
    apply hend
    rcases hs with hs | hs
    · exact Or.inl ⟨hs.1, hs.2.trans hl₀l₁.le⟩
    · exact Or.inr ⟨hu₁u₀.le.trans hs.1, hs.2⟩
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
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨K, O, hK, hKU, hO, hendO, hKO, Phi, hi, hs, hfix, hfixO, hmotion⟩ :=
    exists_relative_ambient_isotopy_of_interval_isotopy_within
      hab hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u hU F hF (by
        intro t ht s hs y hy he
        apply hinj t ht hs hy
        simpa only [heq t ht s hs, heq t ht y hy] using he) (by
        intro t ht s hs
        rw [hFder t ht s hs]
        exact hder t ht s hs) (by
        intro t ht s hs
        rw [heq t ht s (hend hs), heq a ha s (hend hs)]
        exact hstationary t ht s hs) (by
        intro t ht s hs
        rw [heq t ht s (hmid hs)]
        exact htrace t ht s hs)
  refine ⟨K, O, hK, hKU, hO, ?_, hKO, Phi, hi, hs, hfix, hfixO, ?_⟩
  · rintro x ⟨s, hs, rfl⟩
    change f (a, s) ∈ O
    rw [← heq a ha s (hendSmall hs)]
    exact hendO (mem_image_of_mem _ hs)
  · intro t ht s hs
    simpa only [heq a ha s hs, heq t ht s hs] using hmotion t ht s hs

end Poincare.Manifold.Schoenflies
