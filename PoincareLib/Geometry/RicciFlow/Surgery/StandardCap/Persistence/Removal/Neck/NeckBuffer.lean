import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Normalization
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Neck.NeckHeight
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.LengthBarrier
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance

/-!
# An ambient distance buffer about the later surgery sphere

Every sufficiently short ambient path from a central-sphere point
stays within the actual neck. The first-exit argument uses the
compact middle band and its exact height boundary.
Morgan--Tian, Claim 16.10, pp. 374-375; M44 derivation 71.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {g : RiemannianMetric 3 M}

/-- A positive metric ball about any point of the central sphere
is confined in the actual middle band, including against paths
leaving the neck. Source: Claim 16.10; M44 derivation 71. -/
theorem neck_ball_subset_middle_band (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 12) {b : ℝ} (hb0 : 0 < b) (hb : b < N.epsilon⁻¹)
    {p : M} (hp : p ∈ N.central_sphere) :
    g.ball p (Real.sqrt ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center) * b) ⊆
      N.region (-b) b := by
  let c := (1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center
  have hc : 0 < c := div_pos (by linarith) N.scalar_center_pos
  let k := m01RescaledMetric (RiemannianMetric.euclideanMetric 3) c hc
  obtain ⟨hpN, hpH⟩ := (neck_central_iff N).mp hp
  have hpU : p ∈ N.region (-b) b := ⟨hpN, by rw [hpH]; exact ⟨neg_neg_of_pos hb0, hb0⟩⟩
  have hcl := neck_closure_region_subset N hb0 hb
  apply g.ball_subset_of_inverse_length_barrier k (neckHeightVector N)
    (neck_region_isOpen N (-b) b) hpU
  · intro x hx
    exact neckHeightVector_contMDiffAt N (hcl hx)
  · intro x hx w
    exact neckHeightVector_quadratic N hsmall (hcl hx) w
  · intro x hx
    obtain ⟨_hxN, hxH⟩ := neck_frontier_region_height N hb0 hb hx
    have he (v w : E) : (RiemannianMetric.euclideanMetric 3).edist v w = edist v w :=
      (IsRiemannianManifold.out (I := 𝓡 3) v w).symm
    have hdist : (RiemannianMetric.euclideanMetric 3).edist
        (neckHeightVector N p) (neckHeightVector N x) = ENNReal.ofReal b := by
      rw [he]
      simp only [neckHeightVector, hpH, zero_smul, edist_dist, dist_zero_left,
        norm_smul, Real.norm_eq_abs, OrthonormalBasis.norm_eq_one, mul_one, hxH]
    change ENNReal.ofReal (Real.sqrt c * b) ≤
      (m01RescaledMetric (RiemannianMetric.euclideanMetric 3) c hc).edist
        (neckHeightVector N p) (neckHeightVector N x)
    rw [m01RescaledMetric_edist, hdist, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]

/-- The half-width middle band gives an explicit ambient neck
buffer at every point of the surgery sphere. Source: Claim 16.10,
pp. 374-375; M44 derivation 71. -/
theorem neck_ball_subset_carrier (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ 1 / 12) {p : M} (hp : p ∈ N.central_sphere) :
    g.ball p (Real.sqrt ((1 - 6 * N.epsilon) / N.connection.scalarCurvature N.center) *
      (N.epsilon⁻¹ / 2)) ⊆ N.carrier :=
  (neck_ball_subset_middle_band N hsmall (half_pos (inv_pos.mpr N.epsilon_pos))
    (half_lt_self (inv_pos.mpr N.epsilon_pos)) hp).trans (neck_region_subset N _ _)

end PoincareMT.M44
