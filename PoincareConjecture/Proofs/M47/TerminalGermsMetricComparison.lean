import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.UniformMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

theorem terminalGerms_quadratic_of_unit_error
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N) (x : M)
    (hclose : ∀ v w : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 1 → g.tangentNorm x w ≤ 1 →
      |h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
          (mfderiv (𝓡 3) (𝓡 3) f x w) - g.inner x v w| < 1)
    (v : TangentSpace (𝓡 3) x) :
    h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ 4 * g.inner x v v := by
  by_cases hv : v = 0
  · subst v
    simp
  let a := g.tangentNorm x v
  have ha : 0 < a := Real.sqrt_pos.mpr (g.pos x v hv)
  have ha2 : a ^ 2 = g.inner x v v := Real.sq_sqrt (g.pos x v hv).le
  let w : TangentSpace (𝓡 3) x := a⁻¹ • v
  have hw : g.tangentNorm x w = 1 := by
    dsimp [w, RiemannianMetric.tangentNorm]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show a⁻¹ * (a⁻¹ * g.inner x v v) = a⁻¹ ^ 2 * a ^ 2 by rw [ha2]; ring]
    rw [show a⁻¹ ^ 2 * a ^ 2 = 1 by field_simp, Real.sqrt_one]
  have hbound := (le_abs_self _).trans_lt (hclose w w hw.le hw.le)
  simp only [w, map_smul, smul_apply, smul_eq_mul] at hbound
  have hainv : a⁻¹ ^ 2 * a ^ 2 = 1 := by field_simp
  have hpos : 0 < a⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr ha)
  nlinarith [g.pos x v hv]

open ChartDistance

theorem terminalGerms_source_quadratic_bound
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 3))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i)) (hO : SmoothOverlap U hU O)
    [T2Space (Quotient O.setoid)]
    (E : ℕ → Set (Quotient O.setoid)) (hE : ∀ k, IsOpen (E k))
    (hmono : Monotone E) (hcover : (⋃ k, E k) = univ)
    {N : ℕ → Type u} [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    (f : ∀ k, Quotient O.setoid → N k)
    (hf : letI := quotientChartedSpace U hU O
      ∀ k, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k))
    (h : ∀ k, RiemannianMetric 3 (N k))
    (g : ∀ i, CanonicalMetric U hU i) (hg : CompatibleMetrics U hU O g)
    (B : ℕ → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hB : ∀ i, ContinuousOn (B i) (U i))
    (hcoeff : letI : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece U i) :=
        fun i => (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      ∀ i (x : Piece U i) v w, (g i).inner x v w = B i x v w)
    (hconv : ∀ i K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => (h k).pullbackCoefficients (chartParametrization U hU (f k ∘ O.include i)))
      (B i) atTop K) :
    letI := quotientChartedSpace U hU O
    letI := quotient_isManifold U hU O hO
    ∀ K : Set (Quotient O.setoid), IsCompact K → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ≤
            4 * (quotientMetric U hU O hO g hg).inner x v v := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hO
  have herror := source_exhaustion_uniform_metric_error U hU O hO hE hmono hcover f hf
    (fun k _ => h k) (fun i _ => g i) (fun _ => hg)
    (J := {0}) (fun i p => B i p.2)
    (fun i => (hB i).comp continuous_snd.continuousOn (fun _ hp => hp.2))
    (fun i _ _ x => hcoeff i x) (by
      intro i K hK hKU
      have hsub : Prod.snd '' K ⊆ U i := by
        rintro _ ⟨p, hp, rfl⟩
        exact (hKU hp).2
      exact ((hconv i (Prod.snd '' K) (hK.image continuous_snd) hsub).comp Prod.snd).mono
        (subset_preimage_image Prod.snd K))
  intro K hK
  filter_upwards [herror K {0} hK isCompact_singleton Subset.rfl 1 zero_lt_one] with k hk
  intro x hx v
  exact terminalGerms_quadratic_of_unit_error (quotientMetric U hU O hO g hg) (h k)
    (f k) x (hk 0 (mem_singleton 0) x hx) v

end PoincareConjecture.M47
