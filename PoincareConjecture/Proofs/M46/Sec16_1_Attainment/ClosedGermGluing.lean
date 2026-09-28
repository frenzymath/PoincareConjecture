import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePartition









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}




theorem exists_closed_germ_gluing {iota : Type*} [Finite iota] [Nonempty iota]
    (A : Set ℝ) (C : iota → Set ℝ) (hC : ∀ i, IsClosed (C i))
    (hcover : ∀ s ∈ A, ∃ i, s ∈ C i) (f : iota → ℝ → G.Point)
    (hf : ∀ i s, s ∈ A → s ∈ C i →
      ContMDiffWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ (f i) A s)
    (hcompat : ∀ i j s, s ∈ A → s ∈ C i → s ∈ C j →
      f i =ᶠ[𝓝[A] s] f j) :
    ∃ g : ℝ → G.Point, ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ g A ∧
      (∀ i, EqOn g (f i) (A ∩ C i)) ∧
      ∀ i s, s ∈ A → s ∈ C i → g =ᶠ[𝓝[A] s] f i := by
  classical
  let pick (s : ℝ) : iota := if hs : s ∈ A then Classical.choose (hcover s hs)
    else Classical.choice inferInstance
  have hpick (s : ℝ) (hs : s ∈ A) : s ∈ C (pick s) := by
    simpa only [pick, dif_pos hs] using Classical.choose_spec (hcover s hs)
  let g := fun s => f (pick s) s
  have hgerm (i : iota) (s : ℝ) (hs : s ∈ A) (hsi : s ∈ C i) :
      g =ᶠ[𝓝[A] s] f i := by
    have hpiece (j : iota) : ∀ᶠ r in 𝓝[A] s, r ∈ C j → f j r = f i r := by
      by_cases hsj : s ∈ C j
      · filter_upwards [hcompat j i s hs hsj hsi] with r hr
        exact fun _ => hr
      · filter_upwards [nhdsWithin_le_nhds ((hC j).isOpen_compl.mem_nhds hsj)] with r hr
        exact fun hmem => False.elim (hr hmem)
    filter_upwards [Filter.eventually_all.mpr hpiece, self_mem_nhdsWithin] with r hr hra
    exact hr (pick r) (hpick r hra)
  refine ⟨g, ?_, ?_, hgerm⟩
  · intro s hs
    exact (hf (pick s) s hs (hpick s hs)).congr_of_eventuallyEq_of_mem
      (hgerm (pick s) s hs (hpick s hs)) hs
  · intro i s hs
    exact (hgerm i s hs.1 hs.2).eq_of_nhdsWithin hs.1

end PoincareConjecture.Proofs.M46
