import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.PullbackJacobian

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/RegularLimitDensity.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Actual chart-density convergence on the regular-limit region

Morgan-Tian Theorem 11.19(1), p. 279, and Lemma 11.21, p. 280,
supply smooth convergence on the open regular region. The frozen event
predicate yields pointwise Gram-coefficient and volume-density limits,
used in Lemma 17.12, p. 410. See the stage-6 task derivation.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.SurgeryVolume

/-- Open region identifications give the actual partial homeomorphism
used for the regular-limit charts (MT Theorem 11.19, p. 279). -/
def regionOpenPartialHomeomorph {A B : GeneralizedSliceCarrier.{u}}
    {U : Set A.carrier} {V : Set B.carrier} (E : SurgeryRegionEquivalence A B U V)
    (hU : IsOpen U) (hV : IsOpen V) : OpenPartialHomeomorph A.carrier B.carrier where
  toFun := E.map
  invFun := E.inverse
  source := U
  target := V
  map_source' := by
    intro x hx
    exact E.map_image.subset (mem_image_of_mem E.map hx)
  map_target' := by
    intro x hx
    exact E.inverse_image.subset (mem_image_of_mem E.inverse hx)
  left_inv' := E.left_inverse
  right_inv' := E.right_inverse
  open_source := hU
  open_target := hV
  continuousOn_toFun := E.map_smooth.continuousOn
  continuousOn_invFun := E.inverse_smooth.continuousOn

variable {A B : GeneralizedSliceCarrier.{u}}
  {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
  {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}

/-- The zeroth-order part of compact smooth convergence gives the
actual coefficient limit (MT Theorem 11.19(1), p. 279; Lemma 11.21, p. 280). -/
theorem surgeryMetricLimitOn_coefficient_tendsto
    (h : SurgeryMetricLimitOn A B g gT f U T) {q : A.carrier} (hq : q ∈ U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxU : (extChartAt (𝓡 3) q).symm x ∈ U) (i j : Fin 3) :
    Tendsto (fun t => singularMetricCoefficient (g t) q i j x) (𝓝[<] T)
      (𝓝 (surgeryMetricCoefficient gT
        (fun z => f ((extChartAt (𝓡 3) q).symm z)) i j x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd, hbound⟩ := h q hq {x} isCompact_singleton
    (singleton_subset_iff.mpr hx)
    (by simpa only [image_singleton, singleton_subset_iff] using hxU) 0 i j ε hε
  filter_upwards [Ioo_mem_nhdsLT (show T - d < T by linarith)] with t ht
  have hb := hbound t ht.1 ht.2 x (mem_singleton x)
  rw [dist_eq_norm]
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map] using hb

-- The metric form's dependent bilinear coercions require reducible transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Actual Gram Jacobians converge with the regular-limit coefficients
(MT Theorem 11.19(1), p. 279, used in Lemma 17.12, p. 410). -/
theorem surgeryMetricLimitOn_jacobian_tendsto
    (h : SurgeryMetricLimitOn A B g gT f U T) {q : A.carrier} (hq : q ∈ U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxU : (extChartAt (𝓡 3) q).symm x ∈ U) :
    Tendsto (fun t => SurgeryVolume.Measure.pullbackJacobian (g t) (extChartAt (𝓡 3) q).symm x)
      (𝓝[<] T)
      (𝓝 (SurgeryVolume.Measure.pullbackJacobian gT (fun z => f ((extChartAt (𝓡 3) q).symm z)) x)) := by
  have hentry (i j : Fin 3) := surgeryMetricLimitOn_coefficient_tendsto h hq hx hxU i j
  have hmatrix := tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hentry i))
  have hdet := (continuous_id.matrix_det.tendsto _).comp hmatrix
  have hsqrt := (Real.continuous_sqrt.tendsto _).comp hdet
  simpa only [SurgeryVolume.Measure.pullbackJacobian, SurgeryVolume.Measure.pullbackMetricForm,
    ContinuousLinearMap.bilinearComp_apply, singularMetricCoefficient,
    singularTensorCoefficient, surgeryMetricCoefficient, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Function.comp_def, id_eq] using! hsqrt

end PoincareMT.SurgeryVolume
