import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExhaustionBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance rescaledLimitCurvatureCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitCurvatureCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance rescaledLimitCurvatureTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance rescaledLimitCurvatureTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





noncomputable def standardJetCurvatureNorm (J : MetricTwoJet 3) : ℝ :=
  tensorNormFromComponents (Matrix.of (fun i j : Fin 3 => J.1 (e i) (e j)))
    (fun a : Fin 4 → Fin 3 => jetCurvature J (e (a 0)) (e (a 1)) (e (a 2)) (e (a 3)))




theorem standardJetCurvatureNorm_metricTwoJet
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x : E) :
    standardJetCurvatureNorm (metricTwoJet g.euclideanCoefficients x) =
      D.curvatureTensorNorm x := by
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor x
  rw [D.curvatureTensorNorm_eq_tensorNormFromComponents x (e).toBasis A hA]
  unfold standardJetCurvatureNorm
  simp only [jetCurvature_metricTwoJet D]
  rfl





theorem tendsto_standardJetCurvatureNorm
    {alpha : Type*} {l : Filter alpha} {g : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (x : E) {J : alpha → MetricTwoJet 3}
    (hJ : Tendsto J l (𝓝 (metricTwoJet g.euclideanCoefficients x))) :
    Tendsto (fun a => standardJetCurvatureNorm (J a)) l
      (𝓝 (D.curvatureTensorNorm x)) := by
  have hdet : (Matrix.of (fun i j : Fin 3 => g.inner x (e i) (e j))).det ≠ 0 := by
    exact g.pullback_gram_det_ne_zero x LinearMap.id Function.injective_id
  have hI : (metricTwoJet g.euclideanCoefficients x).1.IsInvertible :=
    g.inner_isInvertible x
  have hG (i j : Fin 3) : Tendsto (fun a => (J a).1 (e i) (e j)) l
      (𝓝 ((metricTwoJet g.euclideanCoefficients x).1 (e i) (e j))) := by
    have hc : Continuous (fun A : MetricTwoJet 3 => A.1 (e i) (e j)) := by fun_prop
    exact hc.continuousAt.tendsto.comp hJ
  have hR (a : Fin 4 → Fin 3) :
      Tendsto (fun k => jetCurvature (J k) (e (a 0)) (e (a 1)) (e (a 2)) (e (a 3))) l
        (𝓝 (jetCurvature (metricTwoJet g.euclideanCoefficients x)
          (e (a 0)) (e (a 1)) (e (a 2)) (e (a 3)))) :=
    (contDiffAt_jetCurvature hI _ _ _ _).continuousAt.tendsto.comp hJ
  have h := tendsto_tensorNormFromComponents hG hR hdet
  change Tendsto (fun a => standardJetCurvatureNorm (J a)) l
    (𝓝 (standardJetCurvatureNorm (metricTwoJet g.euclideanCoefficients x))) at h
  simpa only [standardJetCurvatureNorm_metricTwoJet D] using h





theorem standardJetCurvatureNorm_pullbackCoefficients
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) :
    standardJetCurvatureNorm (metricTwoJet (g.pullbackCoefficients f) x) =
      D.curvatureTensorNorm (f x) := by
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt)
      (fun y _ a b => g.symm (f y) _ _)
      (fun y hy a ha => by
        apply g.pos (f y)
        intro hz
        apply ha
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hV.mem_nhds hxV) hmetric
  have htwo : metricTwoJet gE.euclideanCoefficients x =
      metricTwoJet (g.pullbackCoefficients f) x := by
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [← htwo, standardJetCurvatureNorm_metricTwoJet DE]
  exact DE.curvatureTensorNorm_eq_pullback_euclidean D
    (hf.contMDiffAt (hU.mem_nhds hx))
    (eventually_of_mem (hV.mem_nhds hxV) (fun y hy => hinv y (hVU hy)))
    (eventually_of_mem (hV.mem_nhds hxV)
      (fun y hy a b => congrArg (fun C => C a b) (hmetric y hy)))





theorem curvature_locally_bounded_of_rescaled_twoJet_limits
    (g0 : StandardInitialMetric) {lifetime : ℝ}
    (F : RicciFlow 3 E (Ico 0 lifetime))
    (J : ℕ → ℝ → E → MetricTwoJet 3)
    (hconv : ∀ t ∈ Ico 0 lifetime, ∀ x,
      Tendsto (fun k => J k t x) atTop
        (𝓝 (metricTwoJet (F.metric t).euclideanCoefficients x)))
    (hbound : ∀ T0 : ℝ, 0 ≤ T0 → T0 < lifetime →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
        ∀ t ∈ Icc 0 T0, ∀ x ∈ g0.metric.ball 0 R,
          standardJetCurvatureNorm (J k t x) ≤ K) :
    ∀ T0 : ℝ, 0 ≤ T0 → T0 < lifetime →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 T0, ∀ x : E,
        |(F.connection t).curvatureTensorNorm x| ≤ K := by
  intro T0 hT0 hTlife
  obtain ⟨K, hK, hR⟩ := hbound T0 hT0 hTlife
  refine ⟨K, hK, ?_⟩
  apply curvature_bound_of_tendsto_on_standard_exhaustion g0 F.connection
    (fun k t x => standardJetCurvatureNorm (J k t x)) _ hR
  intro t ht x
  exact tendsto_standardJetCurvatureNorm (F.connection t) x
    (hconv t ⟨ht.1, ht.2.trans_lt hTlife⟩ x)

end PoincareConjecture.M44
