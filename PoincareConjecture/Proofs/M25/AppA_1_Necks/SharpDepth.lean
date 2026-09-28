import PoincareConjecture.Proofs.M25.Mathlib.SmoothTentProfile
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

noncomputable def axialDepth (N : EpsilonNeck g) (x : M) : ℝ := by
  classical
  exact if x ∈ N.carrier then
    N.epsilon⁻¹ - |(N.coordinate_inverse x).2| else 0

theorem axialDepth_edist_le (N : EpsilonNeck g) (x y : M) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
      |N.axialDepth x - N.axialDepth y|) ≤ g.edist x y := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let c := N.scale * Real.sqrt (1 - N.epsilon)
  have hc : 0 < c :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  by_cases htop : g.edist x y = ⊤
  · rw [htop]
    exact le_top
  change ENNReal.ofReal (c * |N.axialDepth x - N.axialDepth y|) ≤ _
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  by_contra hnot
  have hgap : 0 < c * |N.axialDepth x - N.axialDepth y| - (g.edist x y).toReal :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let δ := (c * |N.axialDepth x - N.axialDepth y| - (g.edist x y).toReal) / (4 * c)
  have hδ : 0 < δ := div_pos hgap (mul_pos (by norm_num) hc)
  obtain ⟨a, b, φ, ha, hb, hφ, hs, hderiv, hclose⟩ :=
    Real.exists_smooth_tent_profile hL hδ
  let F := N.axialCutoff φ
  have happrox (z : M) : |F z - N.axialDepth z| < δ := by
    by_cases hz : z ∈ N.carrier
    · have hh : 0 ≤ N.epsilon⁻¹ - |(N.coordinate_inverse z).2| :=
        sub_nonneg.mpr (abs_lt.mpr (N.coordinate_inverse_mem z hz).2).le
      simpa only [F, N.axialCutoff_eq_of_mem φ hz, axialDepth, if_pos hz,
        max_eq_right hh] using hclose (N.coordinate_inverse z).2
    · simpa only [F, N.axialCutoff_eq_zero_of_not_mem φ hz, axialDepth, if_neg hz,
        sub_self, abs_zero] using hδ
  let K : ℝ≥0 := ⟨1 / c, (div_pos zero_lt_one hc).le⟩
  have hdist := g.edist_le_mul_edist_of_derivative_bound
    ((N.contMDiff_axialCutoff ha hb hφ hs).of_le (by simp))
    (K := K) (div_pos zero_lt_one hc)
    (N.abs_mvfderiv_axialCutoff_le ha hb hφ hs zero_le_one hderiv) x y
  have hK : ENNReal.ofReal (1 / c) = (K : ℝ≥0∞) := by
    change ENNReal.ofReal (K : ℝ) = (K : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  have hbound : ENNReal.ofReal (c * |F x - F y|) ≤ g.edist x y := by
    calc
      _ = ENNReal.ofReal c * EDist.edist (F x) (F y) := by
        rw [ENNReal.ofReal_mul hc.le, edist_dist, Real.dist_eq]
      _ ≤ ENNReal.ofReal c * ((K : ℝ≥0∞) * g.edist x y) :=
        mul_le_mul' le_rfl hdist
      _ = g.edist x y := by
        rw [← hK, ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
          mul_one_div_cancel hc.ne', ENNReal.ofReal_one, one_mul]
  have hreal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hbound
  have hnear : |N.axialDepth x - N.axialDepth y| < |F x - F y| + 2 * δ := by
    have ht := (abs_sub_le (N.axialDepth x) (F x) (N.axialDepth y)).trans
      (add_le_add le_rfl (abs_sub_le (F x) (F y) (N.axialDepth y)))
    rw [abs_sub_comm (N.axialDepth x) (F x)] at ht
    linarith [happrox x, happrox y]
  have hδeq : 4 * c * δ =
      c * |N.axialDepth x - N.axialDepth y| - (g.edist x y).toReal := by
    dsimp only [δ]
    field_simp
  have hscaled := mul_lt_mul_of_pos_left hnear hc
  nlinarith

theorem edist_center_closure_bounds (N : EpsilonNeck g) {y : M}
    (hy : y ∈ closure N.carrier) (hyout : y ∉ N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹) ≤
        g.edist N.center y ∧
      g.edist N.center y ≤ ENNReal.ofReal
        (N.scale * Real.sqrt (1 + N.epsilon) *
          (N.epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1))) := by
  classical
  have hc := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  refine ⟨?_, ?_⟩
  · simpa only [axialDepth, if_pos hc.1, if_neg hyout, hc.2, abs_zero,
      sub_zero, abs_of_pos hL] using N.axialDepth_edist_le N.center y
  · let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    let R := ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) *
      (N.epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)))
    have hbound : N.carrier ⊆ {z | g.edist N.center z ≤ R} := by
      intro z hz
      have h := N.edist_le_axial_add hc.1 hz
      rw [hc.2, sub_zero] at h
      apply h.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (add_le_add (abs_lt.mpr (N.coordinate_inverse_mem z hz).2).le le_rfl)
        (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
    have hclosed : IsClosed {z | g.edist N.center z ≤ R} :=
      isClosed_le (continuous_const.edist continuous_id) continuous_const
    exact closure_minimal hbound hclosed hy

end PoincareConjecture.EpsilonNeck
