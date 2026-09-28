import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_normalized_flow
    (P : GeneralizedParabolicRescalingTheory.{u} 3)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    {b T : ℝ} (hbt : b < T) (F : RicciFlow 3 M (Icc b T)) :
    ∃ G : RicciFlow 3 M (Icc 0 1), ∀ s : ℝ,
      (∀ x (v w : TangentSpace (𝓡 3) x),
        (G.metric s).inner x v w =
          (T - b)⁻¹ * (F.metric (b + (T - b) * s)).inner x v w) ∧
      (∀ x, (G.connection s).scalarCurvature x =
        (T - b) * (F.connection (b + (T - b) * s)).scalarCurvature x) ∧
      (∀ x, (G.connection s).curvatureTensorNorm x =
        (T - b) * (F.connection (b + (T - b) * s)).curvatureTensorNorm x) ∧
      (∀ x r, (G.metric s).ball x (r / Real.sqrt (T - b)) =
        (F.metric (b + (T - b) * s)).ball x r) ∧
      ∀ E : Set M, calibratedMetricVolume (G.metric s) E =
        ENNReal.ofReal ((Real.sqrt (T - b))⁻¹ ^ 3) *
          calibratedMetricVolume (F.metric (b + (T - b) * s)) E := by
  have hd : 0 < T - b := sub_pos.mpr hbt
  let I : SpacetimeInterval := ⟨Icc b T, ordConnected_Icc, F.nontrivial⟩
  obtain ⟨R⟩ := P.ordinary_flow M I F (T - b)⁻¹ (inv_pos.mpr hd) b
  have hsub : Icc (0 : ℝ) 1 ⊆
      (parabolicInterval (T - b)⁻¹ (inv_pos.mpr hd) b I).domain := by
    intro s hs
    rw [mem_parabolicInterval_iff]
    change b + s / (T - b)⁻¹ ∈ Icc b T
    rw [div_inv_eq_mul]
    constructor <;> nlinarith [hs.1, hs.2]
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow hsub
    ordConnected_Icc (show (Icc (0 : ℝ) 1).Nontrivial from
      ⟨0, by norm_num, 1, by norm_num, by norm_num⟩)
  have hcal (s : ℝ) : MetricHomothetyCalculus
      (F.metric (b + (T - b) * s)) (G.metric s)
      (Diffeomorph.refl (𝓡 3) M ∞) (T - b)⁻¹ := by
    simpa only [G, Poincare.Geometry.RicciFlow.Harnack.restrictFlow,
      parabolicTimeInv, div_inv_eq_mul, mul_comm] using R.metric_calculus s
  have hfactor : Real.rpow (T - b)⁻¹ ((3 : ℝ) / 2) =
      (Real.sqrt (T - b))⁻¹ ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt (3 : ℝ) (inv_pos.mpr hd).le]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by rfl, Real.rpow_natCast, Real.sqrt_inv]
  refine ⟨G, fun s => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x v w
    simpa only [G, Poincare.Geometry.RicciFlow.Harnack.restrictFlow,
      parabolicTimeInv, div_inv_eq_mul, mul_comm] using R.metric_eq s x v w
  · intro x
    simpa only [Diffeomorph.coe_refl, id_eq, div_inv_eq_mul, mul_comm] using
      (hcal s).scalar_eq (F.connection (b + (T - b) * s)) (G.connection s) x
  · intro x
    simpa only [Diffeomorph.coe_refl, id_eq, div_inv_eq_mul, mul_comm] using
      (hcal s).curvature_norm_eq (F.connection (b + (T - b) * s)) (G.connection s) x
  · intro x r
    have hb := (hcal s).ball_image x r
    simpa only [Diffeomorph.coe_refl, image_id, image_id', id_eq, Real.sqrt_inv,
      div_eq_mul_inv, mul_comm] using hb.symm
  · intro E
    have hv := (hcal s).volume_image E
    simpa only [Diffeomorph.coe_refl, image_id, Nat.cast_ofNat, hfactor] using hv

end PoincareConjecture.Proofs.M47
