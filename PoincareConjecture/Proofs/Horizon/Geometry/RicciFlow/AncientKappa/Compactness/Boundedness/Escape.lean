import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.BlowupProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open Poincare.Riemannian.Soul
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RicciFlow.SelectedAncientRescalings

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {b κ : ℝ} {F : RicciFlow 3 M (Iic b)} {p : M}
  (S : SelectedAncientRescalings F κ p)

omit [T2Space M] [SecondCountableTopology M] in

theorem centers_exhaustion_tendsto_atTop
    (hc : MetricComplete (F.metric b))
    (hsec : (F.connection b).NonnegativeSectionalCurvature) :
    letI := (F.metric b).toMetricSpace
    Tendsto (fun i => busemannExhaustion p (S.center i)) atTop atTop := by
  let := (F.metric b).toMetricSpace
  apply Filter.tendsto_atTop.2
  intro r
  have hK := (F.metric b).isCompact_horoballIntersection_of_nonnegativeSectional
    (F.connection b) hc hsec (fun _ _ => rfl) p (le_max_right r 0)
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuous_const.dist continuous_id).continuousOn
  filter_upwards [S.centers_escape.eventually_gt_atTop B] with i hi
  by_contra! hlow
  have hx : S.center i ∈ horoballIntersection p (max r 0) :=
    (busemannExhaustion_le_iff (le_max_right r 0)).mp (hlow.le.trans (le_max_left r 0))
  exact (not_le_of_gt hi) (hB (mem_image_of_mem (fun x => dist p x) hx))

theorem eventually_outside_spherical_half_necks
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ N : EpsilonNeck (F.metric b),
      N.epsilon = ε →
      N.scale = 1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i))) →
      N.center = S.center (σ i) →
      p ∉ N.coordinate_map '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) := by
  have hscale := S.original_scales_tendsto_zero.comp hσ.tendsto_atTop
  have hsmall : ∀ᶠ i in atTop,
      (2 * Real.pi + 2 * ε⁻¹) *
        (1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i)))) < 1 := by
    exact (show Tendsto (fun i => (2 * Real.pi + 2 * ε⁻¹) *
      (1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i)))))
        atTop (𝓝 0) by simpa only [mul_zero, Function.comp_apply] using
          hscale.const_mul (2 * Real.pi + 2 * ε⁻¹)).eventually_lt_const zero_lt_one
  filter_upwards [hsmall, (S.centers_escape.comp hσ.tendsto_atTop).eventually_gt_atTop 1]
    with i hi hd N hNe hNs hNc hp
  obtain ⟨z, hz, hzmap⟩ := hp
  have hzdom : z ∈ N.cylinderDomain := by
    change z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [hNe]
    exact ⟨hz.1, by have := inv_pos.mpr hε; constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hpcarrier : p ∈ N.carrier := hzmap ▸ N.coordinate_map_mem hzdom
  have hdist := N.edist_center_le_of_mem_carrier hpcarrier
  rw [hNe, hNs, hNc] at hdist
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  let := (F.metric b).toMetricSpace
  change dist (S.center (σ i)) p ≤ _ at hreal
  rw [dist_comm] at hreal
  exact (not_lt_of_ge hreal) (hi.trans hd)

theorem eventually_outside_projective_half_slabs
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {ε : ℝ} (hε : 0 < ε)
    (Φ : ℕ → RoundCylinderSpace → M) (q : UnitTwoSphere)
    (hΦ : ∀ᶠ i in atTop,
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (Φ i)
        (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
      RoundCylinderClose ε 0 (fun z v w =>
        (F.connection b).scalarCurvature (S.center (σ i)) *
          roundCylinderPullback (F.metric b) (Φ i) z v w) ∧
      Φ i (q, 0) = S.center (σ i)) :
    ∀ᶠ i in atTop, p ∉ Φ i '' (univ ×ˢ Icc (-ε⁻¹ / 2) (ε⁻¹ / 2)) := by
  let C := Real.sqrt (1 + ε) * (ε⁻¹ / 2 + Real.sqrt 2 * (Real.pi + 1))
  have hsmall : ∀ᶠ i in atTop,
      C * (1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i)))) < 1 := by
    exact (show Tendsto (fun i => C *
      (1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i)))))
        atTop (𝓝 0) by simpa only [mul_zero, Function.comp_apply] using
          (S.original_scales_tendsto_zero.comp hσ.tendsto_atTop).const_mul C).eventually_lt_const zero_lt_one
  filter_upwards [hΦ, hsmall,
    (S.centers_escape.comp hσ.tendsto_atTop).eventually_gt_atTop 1] with i hi hs hd hp
  obtain ⟨z, hz, hzmap⟩ := hp
  have hzi : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ := by
    have := inv_pos.mpr hε
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hzero : (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ := ⟨neg_neg_of_pos (inv_pos.mpr hε), inv_pos.mpr hε⟩
  have hdist := ((F.metric b).edist_le_intrinsicEDist _ (Φ i z) (Φ i (q, 0))).trans
    (intrinsicEDist_cylinderCover_le_axial_add (F.metric b) (Φ i) hε
      (S.scalar_pos (σ i)) hi.1 hi.2.1 hzi hzero)
  rw [hzmap, hi.2.2] at hdist
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  have haxis : |(q, (0 : ℝ)).2 - z.2| ≤ ε⁻¹ / 2 := by
    simp only [zero_sub, abs_neg]
    exact abs_le.mpr ⟨by linarith [hz.2.1], hz.2.2⟩
  have hbound : Real.sqrt ((1 + ε) /
      (F.connection b).scalarCurvature (S.center (σ i))) *
        (|(q, (0 : ℝ)).2 - z.2| + Real.sqrt 2 * (Real.pi + 1)) ≤
      C * (1 / Real.sqrt ((F.connection b).scalarCurvature (S.center (σ i)))) := by
    calc
      _ ≤ Real.sqrt ((1 + ε) /
          (F.connection b).scalarCurvature (S.center (σ i))) *
            (ε⁻¹ / 2 + Real.sqrt 2 * (Real.pi + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add haxis le_rfl) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_div (by positivity)]; dsimp [C]; ring
  exact (not_lt_of_ge (hreal.trans hbound)) (hs.trans hd)

end PoincareConjecture.RicciFlow.SelectedAncientRescalings
