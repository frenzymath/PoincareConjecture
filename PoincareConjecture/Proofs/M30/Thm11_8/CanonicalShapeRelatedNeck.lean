import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalSliceShape










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

private theorem related_inverse_half_lt {r : ℝ} (hr : 4 < r) :
    r ^ (-1 / 2 : ℝ) < 1 / 2 := by
  calc
    _ < (4 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_lt_rpow_of_neg (by norm_num) hr (by norm_num)
    _ = _ := by norm_num [neg_div, Real.rpow_neg, ← Real.sqrt_eq_rpow]



theorem related_neck_data_of_canonical_slice_shape
    {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {epsilon C : ℝ} {x : M} (hx : 4 < D.scalarCurvature x)
    (hshape :
      (∃ N : EpsilonNeck g,
        N.epsilon = 2 * epsilon ∧ N.connection = D ∧ N.center = x) ∨
      (∃ N : EpsilonNeck g, ∃ W : Set M,
        N.epsilon = 2 * epsilon ∧ N.connection = D ∧
        IsOpen W ∧ IsCompact (closure W) ∧ x ∈ W ∧ x ∉ N.carrier ∧
        frontier W = N.central_sphere ∧
        W ∩ N.carrier = N.region (-N.epsilon⁻¹) 0 ∧
        closure W ⊆ g.ball x
          (8 * max 1 C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) ∧
        (4 * max 1 C * D.scalarCurvature x)⁻¹ ≤ N.scale ^ 2 ∧
        N.scale ^ 2 ≤ 4 * max 1 C / D.scalarCurvature x)) :
    ∃ N : EpsilonNeck g,
      N.epsilon = 2 * epsilon ∧ N.connection = D ∧
      D.scalarCurvature x ≤ 4 * max 1 C * D.scalarCurvature N.center ∧
      N.carrier ⊆ g.ball x
        (4 * max 1 C + (2 * Real.pi + 2 * (2 * epsilon)⁻¹) * max 1 C + 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let d := max 1 C
  have hd : 1 ≤ d := le_max_left _ _
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  have hxpos : 0 < D.scalarCurvature x := by linarith
  have hneck : ∃ N : EpsilonNeck g,
      N.epsilon = 2 * epsilon ∧ N.connection = D ∧
      D.scalarCurvature x ≤ 4 * d * D.scalarCurvature N.center ∧
      N.scale ≤ d ∧ g.edist x N.center ≤ ENNReal.ofReal (4 * d) := by
    rcases hshape with ⟨N, hNeps, hNconn, hNcenter⟩ |
      ⟨N, W, hNeps, hNconn, _hW, _hWcompact, _hxW, _hxN,
        hfrontier, _hregion, hball, _hlower, hupper⟩
    · have hscale : N.scale < 1 / 2 := by
        rw [N.scale_eq_scalar, hNconn, hNcenter]
        exact related_inverse_half_lt hx
      refine ⟨N, hNeps, hNconn, ?_, by linarith, ?_⟩
      · rw [hNcenter]
        nlinarith
      · rw [hNcenter]
        simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
        exact bot_le
    · have hcenterpos : 0 < D.scalarCurvature N.center := by
        rw [← hNconn]
        exact N.scalar_center_pos
      have hsquare : N.scale ^ 2 = (D.scalarCurvature N.center)⁻¹ := by
        rw [N.scale_eq_scalar, hNconn,
          ← Real.rpow_mul_natCast hcenterpos.le (-1 / 2) 2]
        norm_num [Real.rpow_neg_one]
      have hunit : D.scalarCurvature N.center * N.scale ^ 2 = 1 := by
        rw [hsquare, mul_inv_cancel₀ hcenterpos.ne']
      have hupper' : N.scale ^ 2 * D.scalarCurvature x ≤ 4 * d :=
        (le_div_iff₀ hxpos).mp hupper
      have hratio : D.scalarCurvature x ≤ 4 * d * D.scalarCurvature N.center := by
        calc
          _ = D.scalarCurvature N.center * (N.scale ^ 2 * D.scalarCurvature x) := by
            rw [← mul_assoc, hunit, one_mul]
          _ ≤ D.scalarCurvature N.center * (4 * d) :=
            mul_le_mul_of_nonneg_left hupper' hcenterpos.le
          _ = _ := mul_comm _ _
      have hsmall : N.scale ^ 2 < d := by
        have hquot : 4 * d / D.scalarCurvature x < d :=
          (div_lt_iff₀ hxpos).mpr (by nlinarith)
        exact hupper.trans_lt hquot
      have hscale : N.scale ≤ d := by nlinarith [N.scale_pos]
      have hcenter : N.center ∈ closure W := by
        apply frontier_subset_closure
        rw [hfrontier]
        exact N.center_on_central_sphere
      have hdist : g.edist x N.center ≤ ENNReal.ofReal (4 * d) := by
        apply (hball hcenter).le.trans
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_lt_mul_of_pos_left (related_inverse_half_lt hx)
          (show (0 : ℝ) < 8 * d by positivity)
        linarith
      exact ⟨N, hNeps, hNconn, hratio, hscale, hdist⟩
  obtain ⟨N, hNeps, hNconn, hratio, hscale, hcenter⟩ := hneck
  refine ⟨N, hNeps, hNconn, hratio, ?_⟩
  intro z hz
  have hcoefficient : 0 < 2 * Real.pi + 2 * (2 * epsilon)⁻¹ := by
    rw [← hNeps]
    exact add_pos (mul_pos (by norm_num) Real.pi_pos)
      (mul_pos (by norm_num) (inv_pos.mpr N.epsilon_pos))
  have hdiam := N.edist_center_le_of_mem_carrier hz
  rw [hNeps] at hdiam
  change g.edist x z < ENNReal.ofReal
    (4 * d + (2 * Real.pi + 2 * (2 * epsilon)⁻¹) * d + 1)
  calc
    _ ≤ g.edist x N.center + g.edist N.center z :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (4 * d) +
        ENNReal.ofReal ((2 * Real.pi + 2 * (2 * epsilon)⁻¹) * d) :=
      add_le_add hcenter (hdiam.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hscale hcoefficient.le)))
    _ = ENNReal.ofReal (4 * d + (2 * Real.pi + 2 * (2 * epsilon)⁻¹) * d) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)

end PoincareConjecture.M30
