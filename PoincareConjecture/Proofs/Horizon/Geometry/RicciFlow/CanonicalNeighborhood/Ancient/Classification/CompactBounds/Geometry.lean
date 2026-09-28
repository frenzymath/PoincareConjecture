import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.SectionalTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.VolumeDiameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Component
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

private theorem sqrt_mul_rpow_neg_half {q : ℝ} (hq : 0 < q) :
    Real.sqrt q * q ^ (-1 / 2 : ℝ) = 1 := by
  rw [neg_div, Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow]
  exact mul_inv_cancel₀ (Real.sqrt_pos.mpr hq).ne'

section Transport

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem orthonormal_pair_independent (g : RiemannianMetric 3 M)
    (x : M) (a b : TangentSpace (𝓡 3) x)
    (ha : g.inner x a a = 1) (hb : g.inner x b b = 1)
    (hab : g.inner x a b = 0) : LinearIndependent ℝ ![a, b] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hna : ‖a‖ = 1 := by
    have h : inner ℝ a a = 1 := ha
    nlinarith [real_inner_self_eq_norm_sq a, norm_nonneg a]
  have hnb : ‖b‖ = 1 := by
    have h : inner ℝ b b = 1 := hb
    nlinarith [real_inner_self_eq_norm_sq b, norm_nonneg b]
  have horth : Orthonormal ℝ (![a, b] : Fin 2 → TangentSpace (𝓡 3) x) := by
    constructor
    · intro i
      fin_cases i
      · exact hna
      · exact hnb
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hab
      · change inner ℝ b a = 0
        rw [real_inner_comm]
        exact hab
      · exact (hij rfl).elim
  exact horth.linearIndependent


theorem AncientKappaNormalization.volume_original_zero
    {K : AncientKappaSolution 3 M} {p : M}
    (A : AncientKappaNormalization K p 0) :
    calibratedMetricVolume (K.flow.metric 0) univ =
      ENNReal.ofReal (A.scale ^ (-3 / 2 : ℝ)) *
        calibratedMetricVolume (A.target.flow.metric 0) univ := by
  have hmetric : MetricHomothety (A.target.flow.metric 0) (K.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) A.scale⁻¹ := by
    intro x v w
    simp only [Diffeomorph.coe_refl, mfderiv_id]
    rw [A.metric_eq, zero_div, zero_add, inv_mul_cancel_left₀ A.scale_pos.ne']
    rfl
  have h := Homothety.homothety_volume_image
    (A.target.flow.metric 0) (K.flow.metric 0)
    (Diffeomorph.refl (𝓡 3) M ∞) A.scale⁻¹ (inv_pos.mpr A.scale_pos) hmetric univ
  simp only [Diffeomorph.coe_refl, image_id, Nat.cast_ofNat] at h
  change calibratedMetricVolume (K.flow.metric 0) univ =
    ENNReal.ofReal ((A.scale⁻¹) ^ (3 / 2 : ℝ)) *
      calibratedMetricVolume (A.target.flow.metric 0) univ at h
  rw [← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [neg_div] using h

end Transport



theorem compact_positive_geometry_of_scaled_diameter
    (P : M27KappaAlternativePredecessors.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ¬ IsRoundAncientKappaSolution K →
        IsCompact (univ : Set M) →
        (Nonempty (ClosedComponentCertificate .threeSphere (univ : Set M)) ∨
          Nonempty (ClosedComponentCertificate .realProjectiveThree (univ : Set M))) →
        (∀ x : M, metricDiameter (K.flow.metric 0) univ <
          D * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)) →
        Nonempty (M27CompactPositiveGeometry K C) := by
  obtain ⟨kappa, hkappa, hnc⟩ := P.universal_noncollapsing
  obtain ⟨c, hc, hsectional⟩ :=
    normalized_compact_uniform_sectional_lower_any_carrier P hkappa hD.le
  obtain ⟨d, v, V, hd, hv, hV, hvolume⟩ :=
    normalized_compact_volume_diameter_bounds P hkappa hD.le
  obtain ⟨L, hL, hscalar⟩ := normalized_compact_uniform_scalar_upper P hkappa hD.le
  let C : ℝ := 1 + D + V + L + c⁻¹ + v⁻¹ + (d⁻¹) ^ 2
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  have hvi : 0 < v⁻¹ := inv_pos.mpr hv
  have hdi : 0 < d⁻¹ := inv_pos.mpr hd
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C := by dsimp [C]; nlinarith [sq_nonneg d⁻¹]
  have hVC : V ≤ C := by dsimp [C]; nlinarith [sq_nonneg d⁻¹]
  have hLC : L < C := by dsimp [C]; nlinarith [sq_nonneg d⁻¹]
  have hic : C⁻¹ ≤ c := by
    have h : c⁻¹ ≤ C := by dsimp [C]; nlinarith [sq_nonneg d⁻¹]
    simpa only [inv_inv] using inv_anti₀ hci h
  have hiv : C⁻¹ ≤ v := by
    have h : v⁻¹ ≤ C := by dsimp [C]; nlinarith [sq_nonneg d⁻¹]
    simpa only [inv_inv] using inv_anti₀ hvi h
  have hCd : C ^ (-1 / 2 : ℝ) ≤ d := by
    have h : (d⁻¹) ^ 2 ≤ C := by dsimp [C]; linarith
    have hroot : d⁻¹ ≤ Real.sqrt C := Real.le_sqrt_of_sq_le h
    rw [neg_div, Real.rpow_neg hC.le, ← Real.sqrt_eq_rpow]
    simpa only [inv_inv] using inv_anti₀ hdi hroot
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K hround hcompact htop hdiam
  let K' : AncientKappaSolution 3 M :=
    { K with kappa := kappa, kappa_pos := hkappa, noncollapsed := hnc K hround }
  have hbounds (x : M) :
      C ^ (-1 / 2 : ℝ) * (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) <
          metricDiameter (K.flow.metric 0) univ ∧
      ENNReal.ofReal (C⁻¹ * (K.flow.connection 0).scalarCurvature x ^ (-3 / 2 : ℝ)) <
          calibratedMetricVolume (K.flow.metric 0) univ ∧
      calibratedMetricVolume (K.flow.metric 0) univ <
          ENNReal.ofReal (C * (K.flow.connection 0).scalarCurvature x ^ (-3 / 2 : ℝ)) ∧
      0 < (K.flow.connection 0).scalarCurvature x ∧
      ∀ y (a b : TangentSpace (𝓡 3) y),
        (K.flow.metric 0).inner y a a = 1 →
        (K.flow.metric 0).inner y b b = 1 →
        (K.flow.metric 0).inner y a b = 0 →
        C⁻¹ * (K.flow.connection 0).scalarCurvature x <
            (K.flow.connection 0).sectionalCurvature y a b ∧
        (K.flow.connection 0).sectionalCurvature y a b <
            C * (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨A⟩ := P.normalization M K' x 0 le_rfl
    have hscale : A.scale = (K.flow.connection 0).scalarCurvature x := A.scale_eq
    have hq : 0 < A.scale := A.scale_pos
    have hs : 0 < Real.sqrt A.scale := Real.sqrt_pos.mpr hq
    have hhalf : 0 < A.scale ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
    have hvolpow : 0 < A.scale ^ (-3 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
    have hnormalizedNc : AncientKappaNoncollapsed A.target.flow kappa := by
      have heq : A.target.kappa = kappa := A.target_kappa
      simpa only [heq] using A.target.noncollapsed
    have hnormalizedDiam : metricDiameter (A.target.flow.metric 0) univ ≤ D := by
      rw [A.metricDiameter_normalized_zero]
      have hx : metricDiameter (K'.flow.metric 0) univ <
          D * A.scale ^ (-1 / 2 : ℝ) := by simpa only [hscale] using hdiam x
      apply le_of_lt
      calc
        Real.sqrt A.scale * metricDiameter (K'.flow.metric 0) univ <
            Real.sqrt A.scale * (D * A.scale ^ (-1 / 2 : ℝ)) :=
          mul_lt_mul_of_pos_left hx hs
        _ = D := by rw [mul_left_comm, sqrt_mul_rpow_neg_half hq, mul_one]
    obtain ⟨hdia, hvolLo, hvolHi⟩ := hvolume A.target x hnormalizedNc
      A.normalized_scalar hcompact hnormalizedDiam
    have hscalarUpper := hscalar A.target x hnormalizedNc
      A.normalized_scalar hcompact hnormalizedDiam
    rw [A.metricDiameter_normalized_zero] at hdia
    rw [← hscale]
    refine ⟨?_, ?_, ?_, hq, ?_⟩
    · apply (mul_lt_mul_iff_right₀ hs).mp
      calc
        Real.sqrt A.scale * (C ^ (-1 / 2 : ℝ) * A.scale ^ (-1 / 2 : ℝ)) =
            C ^ (-1 / 2 : ℝ) := by
          rw [mul_left_comm, sqrt_mul_rpow_neg_half hq, mul_one]
        _ ≤ d := hCd
        _ < Real.sqrt A.scale * metricDiameter (K.flow.metric 0) univ := hdia
    · change ENNReal.ofReal (C⁻¹ * A.scale ^ (-3 / 2 : ℝ)) <
        calibratedMetricVolume (K'.flow.metric 0) univ
      rw [A.volume_original_zero]
      calc
        ENNReal.ofReal (C⁻¹ * A.scale ^ (-3 / 2 : ℝ)) ≤
            ENNReal.ofReal (v * A.scale ^ (-3 / 2 : ℝ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hiv hvolpow.le)
        _ = ENNReal.ofReal (A.scale ^ (-3 / 2 : ℝ)) * ENNReal.ofReal v := by
          rw [ENNReal.ofReal_mul hv.le, mul_comm]
        _ < _ := ENNReal.mul_lt_mul_right
          (ENNReal.ofReal_pos.mpr hvolpow).ne' ENNReal.ofReal_ne_top hvolLo
    · change calibratedMetricVolume (K'.flow.metric 0) univ <
        ENNReal.ofReal (C * A.scale ^ (-3 / 2 : ℝ))
      rw [A.volume_original_zero]
      calc
        ENNReal.ofReal (A.scale ^ (-3 / 2 : ℝ)) *
            calibratedMetricVolume (A.target.flow.metric 0) univ <
            ENNReal.ofReal (A.scale ^ (-3 / 2 : ℝ)) * ENNReal.ofReal V :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hvolpow).ne'
            ENNReal.ofReal_ne_top hvolHi
        _ = ENNReal.ofReal (V * A.scale ^ (-3 / 2 : ℝ)) := by
          rw [ENNReal.ofReal_mul hV.le, mul_comm]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hVC hvolpow.le)
    · intro y a b ha hb hab
      let a' := (Real.sqrt A.scale)⁻¹ • a
      let b' := (Real.sqrt A.scale)⁻¹ • b
      have ha' : (A.target.flow.metric 0).inner y a' a' = 1 :=
        (A.terminalNormalized_inner y a a).trans ha
      have hb' : (A.target.flow.metric 0).inner y b' b' = 1 :=
        (A.terminalNormalized_inner y b b).trans hb
      have hab' : (A.target.flow.metric 0).inner y a' b' = 0 :=
        (A.terminalNormalized_inner y a b).trans hab
      have hlo := hsectional A.target x hnormalizedNc A.normalized_scalar
        hcompact hnormalizedDiam y a' b'
        (orthonormal_pair_independent _ y a' b' ha' hb' hab')
      have hhi : (A.target.flow.connection 0).sectionalCurvature y a' b' ≤ L :=
        (le_abs_self _).trans
          (((A.target.flow.connection 0).abs_sectionalCurvature_le_curvatureTensorNorm
            y a' b').trans ((P.past_norm_le_scalar M A.target 0 0 le_rfl le_rfl y).trans
              (hscalarUpper y)))
      change c < (A.target.flow.connection 0).sectionalCurvature y
        ((Real.sqrt A.scale)⁻¹ • a) ((Real.sqrt A.scale)⁻¹ • b) at hlo
      change (A.target.flow.connection 0).sectionalCurvature y
        ((Real.sqrt A.scale)⁻¹ • a) ((Real.sqrt A.scale)⁻¹ • b) ≤ L at hhi
      rw [A.terminalNormalized_sectional] at hlo hhi
      constructor
      · exact (lt_div_iff₀ hq).mp (hic.trans_lt hlo)
      · exact (div_lt_iff₀ hq).mp (hhi.trans_lt hLC)
  refine ⟨{
    compact := hcompact
    positive := ?_
    topology := htop
    diameter_lower := fun x => (hbounds x).1
    diameter_upper := ?_
    volume_lower := fun x => (hbounds x).2.1
    volume_upper := fun x => (hbounds x).2.2.1
    sectional_bounds := fun x => (hbounds x).2.2.2.2 }⟩
  · intro y a b ha hb hab
    exact (mul_pos (inv_pos.mpr hC) (hbounds y).2.2.2.1).trans
      ((hbounds y).2.2.2.2 y a b ha hb hab).1
  · intro x
    exact (hdiam x).trans_le (mul_le_mul_of_nonneg_right hDC
      (Real.rpow_nonneg (hbounds x).2.2.2.1.le _))

end PoincareConjecture
