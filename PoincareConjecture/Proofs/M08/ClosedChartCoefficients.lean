import PoincareConjecture.Proofs.M08.ChartEulerRegularity
import Mathlib.Analysis.Calculus.TangentCone.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M08

section SpatialDerivative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def spatialWithinFDeriv (C : Set ℝ) (U : Set E) (f : ℝ × E → H)
    (z : ℝ × E) : E →L[ℝ] H :=
  (fderivWithin ℝ f (C ×ˢ U) z).comp (ContinuousLinearMap.inr ℝ ℝ E)

theorem spatialWithinFDeriv_contDiffOn {C : Set ℝ} {U : Set E}
    (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (f : ℝ × E → H)
    (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) :
    ContDiffOn ℝ ∞ (spatialWithinFDeriv C U f) (C ×ˢ U) :=
  (hf.fderivWithin (hC.prod hU.uniqueDiffOn) (by simp)).clm_comp contDiffOn_const

theorem hasFDerivAt_spatialWithin {C : Set ℝ} {U : Set E}
    (hU : IsOpen U) (f : ℝ × E → H) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    {s : ℝ} {x : E} (hs : s ∈ C) (hx : x ∈ U) :
    HasFDerivAt (fun y : E ↦ f (s, y)) (spatialWithinFDeriv C U f (s, x)) x := by
  have hi : HasFDerivAt (fun y : E ↦ (s, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    convert (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x) using 1 <;> ext v <;> simp
  have hd := ((hf (s, x) ⟨hs, hx⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  exact (hd.comp x hi.hasFDerivWithinAt (fun y hy ↦ ⟨hs, hy⟩)).hasFDerivAt
    (hU.mem_nhds hx)

theorem spatialWithinFDeriv_eq_spatialFDeriv {C : Set ℝ} {U : Set E}
    (hU : IsOpen U) (f : ℝ × E → H) {s : ℝ} {x : E}
    (hs : C ∈ 𝓝 s) (hx : x ∈ U) :
    spatialWithinFDeriv C U f (s, x) = spatialFDeriv f (s, x) := by
  unfold spatialWithinFDeriv spatialFDeriv
  rw [fderivWithin_of_mem_nhds (prod_mem_nhds hs (hU.mem_nhds hx))]

end SpatialDerivative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance closedChartCoefficientsDualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance closedChartCoefficientsDualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance closedChartCoefficientsBilinNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance closedChartCoefficientsBilinNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem chartActionMetric_closed_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {C : Set ℝ} (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (chartActionMetric F T x)
      (C ×ˢ (extChartAt (𝓡 n) x).target) := by
  have htimeSmooth : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ T - z.1 ^ 2)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contMDiff.contMDiffOn
  have hpoint : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ (extChartAt (𝓡 n) x).symm z.2)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz ↦ hz.2)
  apply ContMDiffOn.contDiffOn
  apply (metricInChart_joint_contMDiffOn F x).comp (htimeSmooth.prodMk hpoint)
  intro z hz
  refine ⟨htime z.1 hz.1, ?_⟩
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz.2

theorem chartActionPotential_closed_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) {C : Set ℝ}
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (chartActionPotential F T x)
      (C ×ˢ (extChartAt (𝓡 n) x).target) := by
  have htimeSmooth : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ T - z.1 ^ 2)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contMDiff.contMDiffOn
  have hpoint : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ (extChartAt (𝓡 n) x).symm z.2)
      (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz ↦ hz.2)
  have hsc := (hM04.scalar_regular n M J F).comp (htimeSmooth.prodMk hpoint)
    (fun z hz ↦ ⟨htime z.1 hz.1, mem_univ _⟩)
  exact (contDiff_const.mul (contDiff_fst.pow 2)).contDiffOn.mul hsc.contDiffOn

theorem chartMetricOperator_isUnit_of_target {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {s : ℝ} {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) x).target) :
    IsUnit (chartMetricOperator F T x (s, y)) := by
  apply positive_form_operator_isUnit
  intro v hv
  apply metricInChart_pos _ _ v hv
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hy

theorem chartMetricInverse_closed_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) {C : Set ℝ} (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (fun z ↦ Ring.inverse (chartMetricOperator F T x z))
      (C ×ˢ (extChartAt (𝓡 n) x).target) := by
  apply contDiffOn_inverse_operator
  · unfold chartMetricOperator InnerProductSpace.continuousLinearMapOfBilin
    exact contDiffOn_const.clm_comp (chartActionMetric_closed_contDiffOn F T x htime)
  · intro z hz
    exact chartMetricOperator_isUnit_of_target F T x hz.2

def closedChartEulerPhase {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (x : M) (C : Set ℝ)
    (s : ℝ) (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let v := Ring.inverse (chartMetricOperator F T x (s, z.1)) z.2
  (v, chartForceVector
    (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionMetric F T x) (s, z.1))
    (spatialWithinFDeriv C (extChartAt (𝓡 n) x).target (chartActionPotential F T x) (s, z.1)) v)

set_option maxHeartbeats 800000 in
theorem closedChartEulerPhase_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) {C : Set ℝ}
    (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) :
    ContDiffOn ℝ ∞ (Function.uncurry (closedChartEulerPhase F T x C))
      (C ×ˢ ((extChartAt (𝓡 n) x).target ×ˢ univ)) := by
  let Ω := C ×ˢ ((extChartAt (𝓡 n) x).target ×ˢ
    (univ : Set (EuclideanSpace ℝ (Fin n))))
  let k := fun z : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦ (z.1, z.2.1)
  have hk : ContDiffOn ℝ ∞ k Ω := contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmap : MapsTo k Ω (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hB := (chartMetricInverse_closed_contDiffOn F T x htime).comp hk hmap
  have hv := hB.clm_apply contDiffOn_snd.snd
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x
  have hDG := (spatialWithinFDeriv_contDiffOn hC hU _
    (chartActionMetric_closed_contDiffOn F T x htime)).comp hk hmap
  have hDV := (spatialWithinFDeriv_contDiffOn hC hU _
    (chartActionPotential_closed_contDiffOn F hM04 T x htime)).comp hk hmap
  have hQ := (chartForceVector_contDiff (E := EuclideanSpace ℝ (Fin n))).comp_contDiffOn
    ((hDG.prodMk hDV).prodMk hv)
  exact hv.prodMk hQ

theorem closed_chart_spatial_coefficient_bounds {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x : M) {a b : ℝ}
    (hab : a < b) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) x).target)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc a b, ∀ v ∈ K,
      ‖spatialWithinFDeriv (Icc a b) (extChartAt (𝓡 n) x).target
          (chartActionMetric F T x) (s, v)‖ ≤ C ∧
      ‖spatialWithinFDeriv (Icc a b) (extChartAt (𝓡 n) x).target
          (chartActionPotential F T x) (s, v)‖ ≤ C := by
  have hsub : Icc a b ×ˢ K ⊆ Icc a b ×ˢ (extChartAt (𝓡 n) x).target :=
    prod_mono Subset.rfl hKt
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x
  have hG := spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU _
    (chartActionMetric_closed_contDiffOn F T x htime)
  have hV := spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) hU _
    (chartActionPotential_closed_contDiffOn F hM04 T x htime)
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hG.continuousOn.mono hsub)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hV.continuousOn.mono hsub)
  refine ⟨|A| + |B|, by positivity, ?_⟩
  intro s hs v hv
  constructor
  · exact (hA (s, v) ⟨hs, hv⟩).trans (by linarith [le_abs_self A, abs_nonneg B])
  · exact (hB (s, v) ⟨hs, hv⟩).trans (by linarith [le_abs_self B, abs_nonneg A])

end PoincareConjecture.M08
