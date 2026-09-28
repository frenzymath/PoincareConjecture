import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds







set_option autoImplicit false
open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.CoordinateTransition

theorem eventually_derivative_bounds_on_compact_domains
    {n : ℕ} {U V K T : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hT : IsCompact T)
    (hKU : K ⊆ U) (hTV : T ⊆ V)
    {A B : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) U) (hB : ∀ k, ContDiffOn ℝ ∞ (B k) V)
    (hAbound : LocallyEventuallyBoundedDerivatives U A)
    (hBbound : LocallyEventuallyBoundedDerivatives V B)
    (hAsymm : ∀ k x, x ∈ U → ∀ v w, A k x v w = A k x w v)
    (hBsymm : ∀ k x, x ∈ V → ∀ v w, B k x v w = B k x w v)
    (hAlow : ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤ A k x v v)
    (hBlow : ∃ b : ℝ, 0 < b ∧ ∀ᶠ k in atTop,
      ∀ x ∈ T, ∀ v, b * ‖v‖ ^ 2 ≤ B k x v v)
    (hf : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) (interior K))
    (hmap : ∀ᶠ k in atTop, MapsTo (f k) (interior K) (interior T))
    (hmetric : ∀ᶠ k in atTop, ∀ x ∈ interior K, ∀ v w,
      B k (f k x) (fderiv ℝ (f k) x v) (fderiv ℝ (f k) x w) = A k x v w) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ interior K,
      ‖iteratedFDeriv ℝ m (f k) x‖ ≤ C := by
  obtain ⟨a, ha, hAlow⟩ := hAlow
  obtain ⟨b, hb, hBlow⟩ := hBlow
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hAlow.and (hBlow.and (hf.and (hmap.and hmetric))))
  have htail (k : ℕ) := hN (k + N) (Nat.le_add_left N k)
  have hbound := uniform_derivative_bounds_of_local_isometries
    isOpen_interior isOpen_interior (hT.isBounded.subset interior_subset)
    (A := fun k => A (k + N)) (B := fun k => B (k + N)) (f := fun k => f (k + N))
    (fun k => (hA (k + N)).mono (interior_subset.trans hKU))
    (fun k => (hB (k + N)).mono (interior_subset.trans hTV))
    (fun k => (htail k).2.2.1)
    (fun k x hx => hAsymm (k + N) x (hKU (interior_subset hx)))
    (fun k x hx => hBsymm (k + N) x (hTV (interior_subset hx)))
    (lt_min ha hb)
    (fun k x hx v => (mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖v‖)).trans
      ((htail k).1 x (interior_subset hx) v))
    (fun k x hx v => (mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖v‖)).trans
      ((htail k).2.1 x (interior_subset hx) v))
    (fun m => ?_) (fun k => (htail k).2.2.2.1) (fun k => (htail k).2.2.2.2)
  · intro m
    obtain ⟨C, hC⟩ := hbound m
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop N] with k hk x hx
    simpa only [Nat.sub_add_cancel hk] using hC (k - N) x hx
  · obtain ⟨CA, _, hCA⟩ := norm_iteratedFDeriv_le_on_compact hU A hA hAbound hK hKU m
    obtain ⟨CB, _, hCB⟩ := norm_iteratedFDeriv_le_on_compact hV B hB hBbound hT hTV m
    exact ⟨max CA CB,
      fun k x hx => (hCA (k + N) x (interior_subset hx)).trans (le_max_left _ _),
      fun k x hx => (hCB (k + N) x (interior_subset hx)).trans (le_max_right _ _)⟩

end PoincareConjecture.CoordinateTransition

namespace PoincareConjecture.ChartDistance

set_option maxHeartbeats 800000

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {e : ∀ k i, Piece U i → M k}
    {D : ∀ i j, C(Piece U i × Piece U j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k i))

include hD he hc hlower hopen hconn hsmooth in
theorem locallyEventuallyBoundedDerivatives_source_transition
    (g : ∀ k, RiemannianMetric n (M k))
    (hjets : ∀ i, LocallyEventuallyBoundedDerivatives (U i)
      (fun k => (g k).pullbackCoefficients (chartParametrization U hU (e k i))))
    (helliptic : ∀ i K, IsCompact K → K ⊆ U i →
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
        a * ‖v‖ ^ 2 ≤
          (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v v)
    (i j : ι) :
    LocallyEventuallyBoundedDerivatives
      (Subtype.val '' overlap (fun i j => D i j) i j)
      (fun k => coordinateRepresentative U hU
        (fun x => Function.invFun (e k j) (e k i x))) := by
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  intro C hC hCoverlap m
  have hΩ := (hU i).isOpenEmbedding_subtypeVal.isOpenMap _
    (isOpen_overlap hD L he c hc hlower hopen hconn i j)
  obtain ⟨K, hK, hCK, hKΩ⟩ := exists_compact_between hC hΩ hCoverlap
  have hKUi : K ⊆ U i := by
    rintro x hx
    obtain ⟨y, _, rfl⟩ := hKΩ hx
    exact y.property
  have hKi : IsCompact ((Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) ⁻¹' K) :=
    (hU i).isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKUi hx⟩, rfl⟩)
  have hKioverlap : (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) ⁻¹' K ⊆
      overlap (fun i j => D i j) i j := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hKΩ hx
    have : y = x := Subtype.ext heq
    simpa only [this] using hy
  obtain ⟨S, hS, hrep⟩ := exists_compact_source_transition_target
    hD L he c hc hlower hopen hconn hKi hKioverlap
  obtain ⟨T, hT, hST, hTU⟩ := exists_compact_between
    (hS.image continuous_subtype_val) (hU j) (by rintro _ ⟨x, _, rfl⟩; exact x.property)
  have hs (l : ι) (k : ℕ) : ContDiffOn ℝ ∞
      ((g k).pullbackCoefficients (chartParametrization U hU (e k l))) (U l) := by
    intro x hx
    exact ((g k).contDiffAt_pullbackCoefficients
      ((contMDiffOn_chartParametrization U hU (hsmooth k l).contMDiff).contMDiffAt
        ((hU l).mem_nhds hx))).contDiffWithinAt
  have hf : ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      (coordinateRepresentative U hU (fun x => Function.invFun (e k j) (e k i x)))
      (interior K) := by
    filter_upwards [hrep] with k hk
    have hp := (contMDiffOn_chartParametrization U hU (hsmooth k i).contMDiff).mono
      (interior_subset.trans hKUi)
    have hi := contMDiffOn_invFun_of_localDiffeomorph (hsmooth k j) (hopen k j).injective
    have hval := contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞)
      (hU j).isOpenEmbedding_subtypeVal
    apply (hval.comp_contMDiffOn (hi.comp hp ?_)).contDiffOn
    intro x hx
    let x' : Piece U i := ⟨x, hKUi (interior_subset hx)⟩
    have hx' : x' ∈ (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) ⁻¹' K := by
      change x ∈ K
      exact interior_subset hx
    have hxcanon :
        (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x = x' := by
      exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv Subtype.val
        (hU i).isOpenEmbedding_subtypeVal (x := x')
    have hmem := image_subset_range _ _ (hk x' hx').1
    simpa [coordinateRepresentative, chartParametrization, x', hxcanon] using hmem
  have hmap : ∀ᶠ k in atTop, MapsTo
      (coordinateRepresentative U hU (fun x => Function.invFun (e k j) (e k i x)))
      (interior K) (interior T) := by
    filter_upwards [hrep] with k hk x hx
    let x' : Piece U i := ⟨x, hKUi (interior_subset hx)⟩
    have hx' : x' ∈ (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) ⁻¹' K := by
      change x ∈ K
      exact interior_subset hx
    have hxcanon :
        (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x = x' := by
      exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv Subtype.val
        (hU i).isOpenEmbedding_subtypeVal (x := x')
    have hmem := hST (mem_image_of_mem Subtype.val (hk x' hx').2)
    simpa [coordinateRepresentative, x', hxcanon] using hmem
  have hmetric : ∀ᶠ k in atTop, ∀ x ∈ interior K, ∀ v w,
      (g k).pullbackCoefficients (chartParametrization U hU (e k j))
          (coordinateRepresentative U hU (fun x => Function.invFun (e k j) (e k i x)) x)
          (fderiv ℝ (coordinateRepresentative U hU
            (fun x => Function.invFun (e k j) (e k i x))) x v)
          (fderiv ℝ (coordinateRepresentative U hU
            (fun x => Function.invFun (e k j) (e k i x))) x w) =
        (g k).pullbackCoefficients (chartParametrization U hU (e k i)) x v w := by
    filter_upwards [hrep] with k hk x hx v w
    let x' : Piece U i := ⟨x, hKUi (interior_subset hx)⟩
    have hx' : x' ∈ (Subtype.val : Piece U i → EuclideanSpace ℝ (Fin n)) ⁻¹' K := by
      change x ∈ K
      exact interior_subset hx
    simpa [coordinateRepresentative, chartParametrization, x', hx'] using
      (source_transition_pullbackCoefficients U hU (g k) (hsmooth k i).contMDiff
      (hsmooth k j) (hopen k j).injective (hopen k j).isOpen_range x'
      (image_subset_range _ _ (hk x' hx').1) v w)
  obtain ⟨B, hB⟩ := CoordinateTransition.eventually_derivative_bounds_on_compact_domains
    (hU i) (hU j) hK hT hKUi hTU (hs i) (hs j) (hjets i) (hjets j)
    (fun k _ _ _ _ => (g k).symm _ _ _) (fun k _ _ _ _ => (g k).symm _ _ _)
    (helliptic i K hK hKUi) (helliptic j T hT hTU) hf hmap hmetric m
  exact ⟨B, hB.mono fun k hk x hx => hk x (hCK hx)⟩

end PoincareConjecture.ChartDistance
