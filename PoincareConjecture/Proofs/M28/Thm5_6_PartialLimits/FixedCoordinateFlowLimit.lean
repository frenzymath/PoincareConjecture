import PoincareConjecture.Proofs.M28.Mathlib.WithinSmoothCompactness
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinLocalFlows
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.CoordinateFamily









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing PoincareConjecture.ChartDistance
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {tau : ℝ} (F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0))
  (V : Set (EuclideanSpace ℝ (Fin n))) (hV : IsOpen V) [Nonempty V]
  (e : ∀ k, V → M k)

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in




structure FixedCoordinateFlowLimit where

  subsequence : ℕ → ℕ

  subsequence_strictMono : StrictMono subsequence

  coefficients : ℝ × EuclideanSpace ℝ (Fin n) →
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ

  coefficients_smooth : ContDiffOn ℝ ∞ coefficients (Icc (-tau) 0 ×ˢ V)

  jets : ∀ m K, IsCompact K → K ⊆ Icc (-tau) 0 ×ˢ V →
    TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun z => ((F (subsequence k)).metric z.1).pullbackCoefficients
          (chartParametrization (fun _ : Unit => V) (fun _ => hV)
            (i := ()) (e (subsequence k))) z.2) (Icc (-tau) 0 ×ˢ V))
      (iteratedFDerivWithin ℝ m coefficients (Icc (-tau) 0 ×ˢ V)) atTop K

  flow : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    RicciFlow n V (Icc (-tau) 0)

  metric_coefficients :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ t ∈ Icc (-tau) 0, ∀ (x : V) v w,
      (flow.metric t).inner x v w = coefficients (t, x) v w

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in





theorem exists_fixedCoordinateFlowLimit_of_within_bounds
    (htau : 0 < tau) (hconv : Convex ℝ V)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ᶠ k in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ V, ∀ v,
      alpha * ‖v‖ ^ 2 ≤ ((F k).metric t).pullbackCoefficients
        (chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e k)) x v v)
    (hbound : ∀ K, IsCompact K → K ⊆ Icc (-tau) 0 ×ˢ V → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ m
          (fun z => ((F k).metric z.1).pullbackCoefficients
            (chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e k))
            z.2) (Icc (-tau) 0 ×ˢ V) z‖ ≤ B) :
    Nonempty (FixedCoordinateFlowLimit F V hV e) := by
  classical
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let U : Unit → Set (EuclideanSpace ℝ (Fin n)) := fun _ => V
  let hU : ∀ i, IsOpen (U i) := fun _ => hV
  let J := Icc (-tau) 0
  let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
    ((F k).metric z.1).pullbackCoefficients
      (chartParametrization U hU (i := ()) (e k)) z.2
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by linarith)
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith, le_rfl⟩
  let : LocallyCompactSpace J := isClosed_Icc.locallyCompactSpace
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : ∀ _ : ℕ, LocallyCompactSpace (J ×ˢ V) := fun _ =>
    (Homeomorph.Set.prod J V).isOpenEmbedding.locallyCompactSpace
  have hsmooth (k : ℕ) : ContDiffOn ℝ ∞ (f k) (J ×ˢ V) :=
    (F k).smooth.contDiffOn_spacetime_pullbackCoefficients_within hV
      (contMDiffOn_chartParametrization U hU (i := ()) (he k).contMDiff)
  obtain ⟨eta, heta, B, hB, hjets⟩ :=
    exists_common_contDiffOn_subsequence_of_withinJet_bounds
      (fun _ : ℕ => J ×ˢ V)
      (fun _ => (convex_Icc (-tau) 0).prod hconv)
      (fun _ => hJ.prod hV.uniqueDiffOn)
      (fun _ : ℕ => f) (fun _ => hsmooth) (fun _ => hbound)
  have hpoint (t : ℝ) (ht : t ∈ J) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ V) :
      Tendsto (fun k => f (eta k) (t, x)) atTop (𝓝 (B 0 (t, x))) := by
    have hjet := hjets 0 0 {(t, x)} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, hx⟩)
    have hcoeff := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_apply, iteratedFDerivWithin_zero_apply] using
      hcoeff.tendsto_at (mem_singleton (t, x))
  have hex : ∀ t : J, ∃ g : CanonicalMetric U hU (),
      ∀ (x : V) v w, g.inner x v w = B 0 (t, x) v w := by
    intro t
    apply exists_canonicalMetric_of_coordinate_limit U hU
      (fun k => ((F (eta k)).metric t).pullbackCoefficients
        (chartParametrization U hU (i := ()) (e (eta k)))) (fun x => B 0 (t, x)) ()
    · exact (hB 0).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x hx => ⟨t.property, hx⟩)
    · intro k x _ v w
      exact ((F (eta k)).metric t).symm _ _ _
    · intro x hx v w
      exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
        (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) v).continuous.tendsto _).comp
          (hpoint t t.property x hx))
    · intro x hx
      exact ⟨alpha, halpha, (heta.tendsto_atTop.eventually hell).mono
        fun k hk v => hk t t.property x hx v⟩
  choose gSlice hgSlice using hex
  let g : ℝ → CanonicalMetric U hU () := fun t =>
    if ht : t ∈ J then gSlice ⟨t, ht⟩ else gSlice ⟨0, hzero⟩
  have hcoeff : ∀ t ∈ J, ∀ (x : V) v w, (g t).inner x v w = B 0 (t, x) v w := by
    intro t ht x v w
    simpa only [g, dif_pos ht] using hgSlice ⟨t, ht⟩ x v w
  have hg : RiemannianMetric.IsSmoothFamilyOn g J :=
    canonicalMetric_isSmoothFamilyOn_of_coefficients U hU () g (B 0) (hB 0) hcoeff
  obtain ⟨F0, hF0⟩ := exists_ricciFlow_on_within_coordinate_limit U hU hJ
    (fun k => F (eta k)) () (fun k => e (eta k)) (fun k => he (eta k))
    g hg (B 0) hcoeff (hjets 0)
  refine ⟨{
    subsequence := eta
    subsequence_strictMono := heta
    coefficients := B 0
    coefficients_smooth := hB 0
    jets := hjets 0
    flow := F0
    metric_coefficients := ?_ }⟩
  simpa only [hF0] using hcoeff

end PoincareConjecture.M28
