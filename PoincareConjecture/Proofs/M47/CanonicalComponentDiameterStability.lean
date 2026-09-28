import PoincareConjecture.Proofs.M47.CanonicalScalarPowerStability
import PoincareConjecture.Proofs.M47.CanonicalMetricStability
import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [CompactSpace M]



theorem component_diameter_bounds_persist
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) {C : ℝ}
    (N : SingularCComponent (F.metric t.val) (F.connection t.val) C) :
    ∀ᶠ s : Icc a b in 𝓝 t,
      ENNReal.ofReal (C⁻¹ * sSup (range (fun x : N.carrier =>
        (F.connection s.val).scalarCurvature x.val ^ (-1 / 2 : ℝ)))) <
          intrinsicDiameter (F.metric s.val) N.carrier ∧
      intrinsicDiameter (F.metric s.val) N.carrier <
        ENNReal.ofReal (C * sInf (range (fun x : N.carrier =>
          (F.connection s.val).scalarCurvature x.val ^ (-1 / 2 : ℝ)))) := by
  let D := fun s : Icc a b => intrinsicDiameter (F.metric s.val) N.carrier
  let L := fun s : Icc a b => C⁻¹ * sSup (range (fun x : N.carrier =>
    (F.connection s.val).scalarCurvature x.val ^ (-1 / 2 : ℝ)))
  let U := fun s : Icc a b => C * sInf (range (fun x : N.carrier =>
    (F.connection s.val).scalarCurvature x.val ^ (-1 / 2 : ℝ)))
  obtain ⟨hsup, hinf⟩ := continuousAt_scalarPower_extrema_on_compact hC F t N.compact
    (fun _ hx => PoincareConjecture.M47.component_scalar_pos N hx) (-1 / 2 : ℝ)
  have hL : ContinuousAt L t := continuousAt_const.mul hsup
  have hU : ContinuousAt U t := continuousAt_const.mul hinf
  obtain ⟨K, _, hcompare⟩ := exists_compact_slab_metric_volume_comparison F
  let E := fun s : Icc a b => Real.exp (K * |s.val - t.val|)
  have hE : Continuous E :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs))
  have hdiam (s v : Icc a b) :
      D v ≤ ENNReal.ofReal (Real.exp (K * |v.val - s.val|)) * D s := by
    have hnorm := (hcompare s.val s.property v.val v.property).1
    have h := (F.metric s.val).intrinsicDiameter_image_le_mul (F.metric v.val)
      id N.carrier (fun _ _ => contMDiffAt_id) (Real.exp_pos (K * |v.val - s.val|))
      (fun x _ w => by
        simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using hnorm x w)
    simpa only [image_id] using h
  have hboth (s : Icc a b) :
      D s ≤ ENNReal.ofReal (E s) * D t ∧ D t ≤ ENNReal.ofReal (E s) * D s := by
    refine ⟨hdiam t s, ?_⟩
    simpa only [E, abs_sub_comm] using hdiam s t
  have hfinite : D t ≠ ⊤ := ne_of_lt (N.diameter_upper.trans_le le_top)
  have hlowContinuous : ContinuousAt (fun s : Icc a b => ENNReal.ofReal (E s * L s)) t :=
    ENNReal.continuous_ofReal.continuousAt.comp (hE.continuousAt.mul hL)
  have hlow : ∀ᶠ s : Icc a b in 𝓝 t, ENNReal.ofReal (E s * L s) < D t :=
    hlowContinuous.eventually_lt continuousAt_const (by
      simpa only [E, sub_self, abs_zero, mul_zero, Real.exp_zero, one_mul]
        using N.diameter_lower)
  have hhighContinuous : ContinuousAt (fun s : Icc a b => ENNReal.ofReal (E s) * D t) t :=
    (ENNReal.continuous_mul_const hfinite).continuousAt.comp
      (ENNReal.continuous_ofReal.continuousAt.comp hE.continuousAt)
  have hhigh : ∀ᶠ s : Icc a b in 𝓝 t,
      ENNReal.ofReal (E s) * D t < ENNReal.ofReal (U s) :=
    hhighContinuous.eventually_lt (ENNReal.continuous_ofReal.continuousAt.comp hU) (by
      simpa only [E, sub_self, abs_zero, mul_zero, Real.exp_zero,
        ENNReal.ofReal_one, one_mul] using N.diameter_upper)
  filter_upwards [hlow, hhigh] with s hsLow hsHigh
  change ENNReal.ofReal (L s) < D s ∧ D s < ENNReal.ofReal (U s)
  constructor
  · rw [ENNReal.ofReal_mul (Real.exp_pos (K * |s.val - t.val|)).le] at hsLow
    by_contra hnot
    have hle : D s ≤ ENNReal.ofReal (L s) := le_of_not_gt hnot
    exact (not_lt_of_ge ((hboth s).2.trans (mul_le_mul' le_rfl hle))) hsLow
  · exact (hboth s).1.trans_lt hsHigh

end PoincareConjecture.Proofs.M47
