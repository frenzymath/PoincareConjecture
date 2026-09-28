import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Prepend
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Invariants
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.SuccessorThreeQuarter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InnerSlabCover








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NeckOnlyCover

open EpsilonNeck BalancedNeckChain

theorem exists_selected_prepend_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (H : NeckOnlyCover g), H.epsilon ≤ ε₀ →
        ∀ C : BalancedNeckChain g H.epsilon, C.IsSelectedFrom H → C.HasQuarterCapture →
        (∀ N ∈ H.necks, N.IsSeparating) →
        ∀ P ∈ H.necks, P.center ∈ H.X →
        ∀ a ∈ C.shape.active, a - 1 ∉ C.shape.active →
          P.center ∈ closure ((C.neck a).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) →
          P.center ∉ C.unionOpen →
          ∃ D : BalancedNeckChain g H.epsilon,
            C.IsExtension D ∧ D.IsSelectedFrom H ∧ D.HasQuarterCapture ∧
              a - 1 ∈ D.shape.active := by
  obtain ⟨ε₁, hε₁, hsmall, hprepend⟩ := exists_prepend_at_outer_frontier_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hoverlap⟩ := exists_frontier_reversal_balanced_overlap.{u}
  obtain ⟨ε₃, hε₃, _, hscale⟩ := exists_scale_comparison_on_closure.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε C hselected hcapture hsep P hP hPx
    a ha hprev hfront hout
  have hbounds : H.epsilon ≤ ε₁ ∧ H.epsilon ≤ ε₂ ∧ H.epsilon ≤ ε₃ := by
    simpa only [le_min_iff] using hε
  have heA := C.epsilon_eq a ha
  have heP := H.neck_epsilon P hP
  have hsepA := hselected.isSeparating hsep ha
  have houtA : P.center ∉ (C.neck a).carrier := by
    intro hx
    exact hout (mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩)
  obtain ⟨Q, hsame, hpositive, hnegative, hwithin, _, _⟩ :=
    hoverlap (C.neck a).reversed P (by simpa only [reversed_isSeparating] using hsepA)
      (by simpa only [reversed_epsilon, heA] using hbounds.2.1)
      (heP.trans heA.symm)
      (by simpa only [reversed_region, reversed_epsilon, heA, neg_div] using hfront)
      houtA
  have hsame' : Q.reversed.SameUpToReversal P := Q.reversed_sameUpToReversal.trans hsame
  have heQ : Q.reversed.epsilon = H.epsilon := hsame'.epsilon_eq.trans heP
  have hfrontQ : Q.reversed.center ∈ closure
      ((C.neck a).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) := by
    rwa [hsame'.center_eq]
  have hpos : Q.reversed.region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆
      (C.neck a).carrier := by
    simpa only [reversed_epsilon, reversed_region, reversed_carrier, heA, neg_div]
      using hnegative
  have hneg : (C.neck a).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2) ⊆
      Q.reversed.carrier := by
    simpa only [reversed_epsilon, reversed_region, reversed_carrier, heA, neg_div]
      using hpositive
  have hwithin' : Q.reversed.carrier ∩ (C.neck a).carrier ⊆
      Q.reversed.region (-H.epsilon⁻¹ / 2) H.epsilon⁻¹ ∩
        (C.neck a).region (-H.epsilon⁻¹) (H.epsilon⁻¹ / 2) := by
    intro x hx
    have h := hwithin ⟨hx.2, hx.1⟩
    constructor
    · simpa only [reversed_region, reversed_epsilon, heA, neg_div, neg_neg] using h.2
    · simpa only [reversed_region, reversed_epsilon, heA, neg_div, neg_neg] using h.1
  obtain ⟨D, hext, hshape, hsource, hneck⟩ := hprepend C Q.reversed P hbounds.1 heQ hsame'
    a ha hprev hsepA hfrontQ (by rwa [hsame'.center_eq]) hpos hneg hwithin'
  have hnew : a - 1 ∈ D.shape.active := by
    rw [hshape, ChainShape.extendLeft_active ha hprev]
    exact mem_insert _ _
  refine ⟨D, hext, ?_, ?_, hnew⟩
  · apply hselected.of_insert hext (j := a - 1) (S := P)
      (by rw [hshape, ChainShape.extendLeft_active ha hprev]) hsource hP
    rwa [hneck, hsame'.center_eq]
  · apply hcapture.of_prepend hext ha hprev hshape
    rw [hneck]
    have hs := (hscale (C.neck a) Q.reversed
      (by simpa only [heA] using hbounds.2.2)
      (closure_mono ((C.neck a).region_subset_carrier _ _) hfrontQ)).1
    simpa only [heA] using (C.neck a).negative_quarter_subset_frontier_neck_inner_slab
      Q.reversed (by rw [heA]; exact hbounds.1.trans (hsmall.trans (by norm_num)))
      (heQ.trans heA.symm) hs (by simpa only [heA] using hfrontQ)

end PoincareConjecture.NeckOnlyCover
