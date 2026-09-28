import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.MetricUniform
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.SpacetimeMetricConvergence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hs : SmoothOverlap U hU O)

include hs in
theorem inducedForm_chart_coefficients
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : Quotient O.setoid → M) (i : ι) (x : Piece U i) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ f (O.include i x) →
      let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
        inducedForm (I := 𝓡 n) (J := 𝓡 n) g f (O.include i x)
      let D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        mfderiv (𝓡 n) (𝓡 n) (O.include i) x
      A.bilinearComp D D =
        g.pullbackCoefficients (chartParametrization U hU (f ∘ O.include i)) x := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro hf
  have hi := (include_isLocalDiffeomorph U hU O hs i).contMDiff x
  have hd := mfderiv_chartParametrization U hU x (hf.comp x hi)
  rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))] at hd
  ext v w
  change g.inner (f (O.include i x))
      (mfderiv (𝓡 n) (𝓡 n) f (O.include i x)
        (mfderiv (𝓡 n) (𝓡 n) (O.include i) x v))
      (mfderiv (𝓡 n) (𝓡 n) f (O.include i x)
        (mfderiv (𝓡 n) (𝓡 n) (O.include i) x w)) =
    g.inner (chartParametrization U hU (f ∘ O.include i) x)
      (mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU (f ∘ O.include i)) x v)
      (mfderiv (𝓡 n) (𝓡 n) (chartParametrization U hU (f ∘ O.include i)) x w)
  rw [chartParametrization_apply, hd]
  rfl

theorem source_exhaustion_uniform_metric_error
    [T2Space (Quotient O.setoid)]
    {E : ℕ → Set (Quotient O.setoid)}
    (hE : ∀ k, IsOpen (E k)) (hEmono : Monotone E) (hEcover : (⋃ k, E k) = univ)
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (F : ∀ k, Quotient O.setoid → M k)
    (hF : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) (E k))
    (gSource : ∀ k, ℝ → RiemannianMetric n (M k))
    (g : ∀ i, ℝ → CanonicalMetric U hU i)
    (hg : ∀ t, CompatibleMetrics U hU O (fun i => g i t))
    {J : Set ℝ}
    (B : ι → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ∀ i, ContinuousOn (B i) (J ×ˢ U i))
    (hcoeff : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i t, t ∈ J → ∀ (x : Piece U i) v w, (g i t).inner x v w = B i (t, x) v w)
    (hconv : ∀ i C, IsCompact C → C ⊆ J ×ˢ U i → TendstoUniformlyOn
      (fun k p => (gSource k p.1).pullbackCoefficients
        (chartParametrization U hU (F k ∘ O.include i)) p.2) (B i) atTop C) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hs
    ∀ K I, IsCompact K → IsCompact I → I ⊆ J → ∀ ε > 0,
      ∀ᶠ k in atTop, ∀ t ∈ I, ∀ x ∈ K, ∀ v w : TangentSpace (𝓡 n) x,
        Real.sqrt ((quotientMetric U hU O hs (fun i => g i t) (hg t)).inner x v v) ≤ 1 →
        Real.sqrt ((quotientMetric U hU O hs (fun i => g i t) (hg t)).inner x w w) ≤ 1 →
        |(gSource k t).inner (F k x) (mfderiv (𝓡 n) (𝓡 n) (F k) x v)
            (mfderiv (𝓡 n) (𝓡 n) (F k) x w) -
          (quotientMetric U hU O hs (fun i => g i t) (hg t)).inner x v w| < ε := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hs
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 n) ∞ (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
  apply eventually_tensor_error_lt_on_compact_quotient U hU O hs g hg
    (A := fun k t => inducedForm (I := 𝓡 n) (J := 𝓡 n) (gSource k t) (F k))
  · intro i
    have h := (hB i).comp (s := J ×ˢ (univ : Set (Piece U i))) (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, p.2.property⟩)
    apply h.congr
    intro p hp
    ext v w
    exact hcoeff i p.1 hp.1 p.2 v w
  · intro i I C hI hIJ hC
    let a : ℝ × Piece U i → ℝ × EuclideanSpace ℝ (Fin n) := fun p => (p.1, p.2)
    have ha : Continuous a := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hIC : IsCompact (a '' (I ×ˢ C)) := (hI.prod hC).image ha
    have hICU : a '' (I ×ˢ C) ⊆ J ×ˢ U i := by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨hIJ hp.1, p.2.property⟩
    have ht := ((hconv i _ hIC hICU).comp a).mono (subset_preimage_image a _)
    have htarget : EqOn (B i ∘ a)
        (fun p : ℝ × Piece U i => (g i p.1).inner p.2) (I ×ˢ C) := by
      intro p hp
      ext v w
      exact (hcoeff i p.1 (hIJ hp.1) p.2 v w).symm
    apply (ht.congr_right htarget).congr
    have hCQ : IsCompact (O.include i '' C) :=
      hC.image (O.include_isOpenEmbedding i).continuous
    obtain ⟨N, hN⟩ := hCQ.elim_directed_cover E hE
      (by rw [hEcover]; exact subset_univ _) hEmono.directed_le
    filter_upwards [eventually_ge_atTop N] with k hk p hp
    exact (inducedForm_chart_coefficients U hU O hs (gSource k p.1) (F k) i p.2
      ((hF k ⟨O.include i p.2, hEmono hk (hN (mem_image_of_mem _ hp.2))⟩).contMDiffAt)).symm

end PoincareConjecture.ChartDistance
