import PoincareConjecture.Definitions.M27CanonicalGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Cap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Length
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.CurvatureTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology Pointwise

universe u

namespace PoincareConjecture.AncientKappaNormalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M} {b C : ℝ}

private theorem terminalMetricHomothety (A : AncientKappaNormalization K p b) :
    MetricHomothety (K.flow.metric b) (A.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) A.scale := by
  intro x v w
  simpa [Diffeomorph.coe_refl, mfderiv_id] using A.metric_eq 0 x v w


theorem metricDiameter_normalized_zero (A : AncientKappaNormalization K p b) (X : Set M) :
    metricDiameter (A.target.flow.metric 0) X =
      Real.sqrt A.scale * metricDiameter (K.flow.metric b) X := by
  have hdist (x y : M) : ((A.target.flow.metric 0).edist x y).toReal =
      Real.sqrt A.scale * ((K.flow.metric b).edist x y).toReal := by
    have h := Homothety.homothety_edist (K.flow.metric b) (A.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) A.scale A.scale_pos A.terminalMetricHomothety x y
    change (A.target.flow.metric 0).edist x y = _ at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  simp only [metricDiameter, hdist]
  simpa only [Set.smul_set_range, smul_eq_mul] using
    Real.sSup_smul_of_nonneg (Real.sqrt_nonneg A.scale)
      (Set.range (fun q : X × X => ((K.flow.metric b).edist q.1 q.2).toReal))


theorem scalarCurvatureSup_normalized_zero (A : AncientKappaNormalization K p b) :
    scalarCurvatureSup (A.target.flow.metric 0) (A.target.flow.connection 0) =
      A.scale⁻¹ * scalarCurvatureSup (K.flow.metric b) (K.flow.connection b) := by
  have heq : (A.target.flow.connection 0).scalarCurvature =
      fun x => A.scale⁻¹ * (K.flow.connection b).scalarCurvature x := by
    funext x
    have h := A.scalar_eq 0 le_rfl x
    rw [zero_div, add_zero] at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  simp only [scalarCurvatureSup, heq]
  simpa only [Set.smul_set_range, smul_eq_mul, mul_comm] using
    Real.sSup_smul_of_nonneg (inv_nonneg.mpr A.scale_pos.le)
      (Set.range (K.flow.connection b).scalarCurvature)


theorem terminalNormalized_inner (A : AncientKappaNormalization K p b)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    (A.target.flow.metric 0).inner x
        ((Real.sqrt A.scale)⁻¹ • v) ((Real.sqrt A.scale)⁻¹ • w) =
      (K.flow.metric b).inner x v w := by
  rw [A.metric_eq, zero_div, add_zero]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hs := Real.sq_sqrt A.scale_pos.le
  field_simp [(Real.sqrt_pos.mpr A.scale_pos).ne']
  rw [hs]


theorem terminalNormalized_sectional (A : AncientKappaNormalization K p b)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    (A.target.flow.connection 0).sectionalCurvature x
        ((Real.sqrt A.scale)⁻¹ • v) ((Real.sqrt A.scale)⁻¹ • w) =
      (K.flow.connection b).sectionalCurvature x v w / A.scale := by
  rw [MetricSurgery.sectionalCurvature_smul_pair _ _ _ _
    (inv_ne_zero (Real.sqrt_pos.mpr A.scale_pos).ne')
    (inv_ne_zero (Real.sqrt_pos.mpr A.scale_pos).ne')]
  simpa [Diffeomorph.coe_refl, mfderiv_id] using
    Homothety.homothety_sectionalCurvature_eq (K.flow.metric b) (A.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) A.scale A.scale_pos A.terminalMetricHomothety
      (K.flow.connection b) (A.target.flow.connection 0) x v w

private theorem terminalNormalized_scalarPower (A : AncientKappaNormalization K p b)
    (hb : b ≤ 0) (x : M) :
    (A.target.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) =
      Real.sqrt A.scale * (K.flow.connection b).scalarCurvature x ^ (-1 / 2 : ℝ) := by
  have hR : 0 ≤ (K.flow.connection b).scalarCurvature x := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      (K.flow.connection b).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x
        (K.nonnegative_curvature_operator b hb x) _ _
  rw [A.scalar_eq 0 le_rfl, zero_div, add_zero, Real.div_rpow hR A.scale_pos.le,
    neg_div, Real.rpow_neg A.scale_pos.le, div_inv_eq_mul, Real.sqrt_eq_rpow, mul_comm]


theorem canonicalComponentFromNormalization (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : M27CanonicalComponent A.target 0 C) : M27CanonicalComponent K b C := by
  have hs : 0 < Real.sqrt A.scale := Real.sqrt_pos.mpr A.scale_pos
  have hsup : sSup (Set.range (fun x : M =>
      (A.target.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ))) =
      Real.sqrt A.scale * sSup (Set.range (fun x : M =>
        (K.flow.connection b).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
    simp only [A.terminalNormalized_scalarPower hb]
    simpa only [Set.smul_set_range, smul_eq_mul] using
      Real.sSup_smul_of_nonneg hs.le (Set.range (fun x : M =>
        (K.flow.connection b).scalarCurvature x ^ (-1 / 2 : ℝ)))
  have hinf : sInf (Set.range (fun x : M =>
      (A.target.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ))) =
      Real.sqrt A.scale * sInf (Set.range (fun x : M =>
        (K.flow.connection b).scalarCurvature x ^ (-1 / 2 : ℝ))) := by
    simp only [A.terminalNormalized_scalarPower hb]
    simpa only [Set.smul_set_range, smul_eq_mul] using
      Real.sInf_smul_of_nonneg hs.le (Set.range (fun x : M =>
        (K.flow.connection b).scalarCurvature x ^ (-1 / 2 : ℝ)))
  refine { N with
    time_mem := hb
    positive := ?_
    scalar_sup_pos := ?_
    uniform_sectional_lower := ?_
    diameter_lower := ?_
    diameter_upper := ?_ }
  · intro x v w hv hw hvw
    have h := N.positive x ((Real.sqrt A.scale)⁻¹ • v) ((Real.sqrt A.scale)⁻¹ • w)
      (by simpa only [A.terminalNormalized_inner] using hv)
      (by simpa only [A.terminalNormalized_inner] using hw)
      (by simpa only [A.terminalNormalized_inner] using hvw)
    rw [A.terminalNormalized_sectional] at h
    exact (div_pos_iff_of_pos_right A.scale_pos).mp h
  · have h := N.scalar_sup_pos
    rw [A.scalarCurvatureSup_normalized_zero] at h
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr A.scale_pos)).mp h
  · obtain ⟨B, hB, hbound⟩ := N.uniform_sectional_lower
    refine ⟨B, hB, ?_⟩
    intro x v w hv hw hvw
    have h := hbound x ((Real.sqrt A.scale)⁻¹ • v) ((Real.sqrt A.scale)⁻¹ • w)
      (by simpa only [A.terminalNormalized_inner] using hv)
      (by simpa only [A.terminalNormalized_inner] using hw)
      (by simpa only [A.terminalNormalized_inner] using hvw)
    rw [A.terminalNormalized_sectional, A.scalarCurvatureSup_normalized_zero] at h
    apply (div_le_div_iff_of_pos_right A.scale_pos).mp
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · have h := N.diameter_lower
    rw [hsup, A.metricDiameter_normalized_zero] at h
    apply (mul_lt_mul_iff_right₀ hs).mp
    simpa only [mul_left_comm] using h
  · have h := N.diameter_upper
    rw [hinf, A.metricDiameter_normalized_zero] at h
    apply (mul_lt_mul_iff_right₀ hs).mp
    simpa only [mul_left_comm] using h

end PoincareConjecture.AncientKappaNormalization
