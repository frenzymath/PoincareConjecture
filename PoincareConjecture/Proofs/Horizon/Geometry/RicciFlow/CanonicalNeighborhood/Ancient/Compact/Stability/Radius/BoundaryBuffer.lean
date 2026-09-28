import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.CollarDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem EpsilonNeck.closure_ball_four_scale_subset
    (N : EpsilonNeck g) (hepsilon : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.central_sphere) :
    closure (g.ball x (4 * N.scale)) ⊆ N.carrier := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hscale := N.scale_pos
  have hinv : (200 : ℝ) ≤ N.epsilon⁻¹ := by
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le N.epsilon_pos hepsilon
  have h32 : (32 : ℝ) < N.epsilon⁻¹ := by linarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hlength : (2 * Real.pi + 4) * N.scale <
      N.scale * Real.sqrt (1 - N.epsilon) * 32 := by
    have hh := mul_le_mul_of_nonneg_left hsqrt N.scale_pos.le
    have hpi := mul_lt_mul_of_pos_right Real.pi_lt_four N.scale_pos
    nlinarith [N.scale_pos]
  have hball : g.ball x (4 * N.scale) ⊆ N.closedCollar 32 := by
    intro y hy
    by_contra hout
    have hlower := N.edist_center_lower_of_not_mem_closedCollar (by norm_num) h32 hout
    have hsphere := N.edist_central_sphere_le_two_pi_mul_scale N.center_on_central_sphere hx
    have hupper : g.edist N.center y ≤ ENNReal.ofReal ((2 * Real.pi + 4) * N.scale) := by
      apply (edist_triangle N.center x y).trans
      calc
        g.edist N.center x + g.edist x y ≤
            ENNReal.ofReal ((2 * Real.pi) * N.scale) + ENNReal.ofReal (4 * N.scale) :=
          add_le_add hsphere hy.le
        _ = ENNReal.ofReal ((2 * Real.pi + 4) * N.scale) := by
          rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (2 * Real.pi) * N.scale)
            (by linarith [N.scale_pos] : 0 ≤ 4 * N.scale)]
          congr 1
          ring
    exact (not_lt_of_ge (hlower.trans hupper))
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (by positivity : 0 ≤ (2 * Real.pi + 4) * N.scale)).mpr hlength)
  exact (closure_minimal hball (N.isCompact_closedCollar h32).isClosed).trans
    (N.closedCollar_subset_carrier h32)

theorem CapCertificate.closure_ball_boundary_scale_subset (A : CapCertificate g)
    {x : M} (hx : x ∈ A.boundary_sphere) :
    closure (g.ball x (4 * A.boundary_neck.scale)) ⊆ A.carrier := by
  apply (A.boundary_neck.closure_ball_four_scale_subset ?_ ?_).trans A.boundary_neck_subset
  · simpa only [A.boundary_neck_epsilon] using A.epsilon_le_threshold
  · simpa only [A.boundary_eq_neck_sphere] using hx

theorem EpsilonNeck.exists_scalar_radius_boundary_buffer :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
        ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ epsilon₀ →
          ∀ x ∈ N.central_sphere, ∀ r : ℝ, 0 < r →
            D.scalarCurvature x ≤ r⁻¹ ^ 2 →
            r < 2 * N.scale ∧ closure (g.ball x (2 * r)) ⊆ N.carrier := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hcurv⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hepsilon x hx r hr hR
  have hxN := N.central_sphere_subset hx
  have hclose : |N.scale ^ 2 * D.scalarCurvature x - 1| < 1 / 2 := by
    simpa only [Prod.eta, N.coordinate_map_coordinate_inverse hxN] using
      (hcurv N D hepsilon (N.coordinate_inverse x).1 (N.coordinate_inverse_mem x hxN).2).1
  have hrlower : 1 / 2 < N.scale ^ 2 * D.scalarCurvature x := by
    have h := (abs_lt.mp hclose).1
    linarith
  have hupper : r ^ 2 * D.scalarCurvature x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hR (sq_nonneg r)
    have hcancel : r ^ 2 * r⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
    simpa only [hcancel] using h
  have hproduct := mul_lt_mul_of_pos_left hrlower (sq_pos_of_pos hr)
  have hbound := mul_le_mul_of_nonneg_left hupper (sq_nonneg N.scale)
  have hlt : r < 2 * N.scale := by nlinarith [N.scale_pos]
  refine ⟨hlt, ?_⟩
  apply (closure_mono ?_).trans
    (N.closure_ball_four_scale_subset (hepsilon.trans hsmall) hx)
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : 2 * r ≤ 4 * N.scale))

end PoincareConjecture
