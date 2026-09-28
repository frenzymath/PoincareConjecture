import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private theorem coordinate_map_mfderiv_inverse_product {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) = v := by
  have hh := mfderiv_comp x
    ((N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds (N.coordinate_inverse_mem x hx))).mdifferentiableAt
      (by simp))
    ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp))
  have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.coordinate_map_coordinate_inverse hy
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  exact (congrArg (fun L => L v) hh).symm

private theorem axial_mvfderiv {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v =
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v).2 := by
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  change mvfderiv (𝓡 3) (Prod.snd ∘ N.coordinate_inverse) x v = _
  rw [mvfderiv, mfderiv_comp x
    ((contMDiff_snd (n := ∞)).mdifferentiableAt (by simp)) hi, mfderiv_snd]
  rfl


theorem axial_mvfderiv_bound {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    N.scale * Real.sqrt (1 - N.epsilon) *
        |mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v| ≤
      g.tangentNorm x v := by
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v
  have h := (N.pullback_metric_bounds (N.coordinate_inverse_mem x hx).2 w).1
  unfold roundCylinderPullback at h
  rw [N.coordinate_map_mfderiv_inverse_product hx v,
    N.coordinate_map_coordinate_inverse hx] at h
  have hw : w.2 ^ 2 ≤ EvolvingRoundCylinderMetric 0 (N.coordinate_inverse x) w w := by
    dsimp only [EvolvingRoundCylinderMetric]
    nlinarith [real_inner_self_nonneg (x := mfderiv (𝓡 2) (𝓡 3)
      (fun q : UnitTwoSphere => q.1) (N.coordinate_inverse x).1 w.1)]
  have hε : 0 < 1 - N.epsilon := by linarith [N.epsilon_lt_half]
  have hs : 0 ≤ (1 - N.epsilon) * N.scale ^ 2 := by positivity
  have hsq := (mul_le_mul_of_nonneg_left hw hs).trans h
  rw [N.axial_mvfderiv hx v]
  change N.scale * Real.sqrt (1 - N.epsilon) * |w.2| ≤ Real.sqrt (g.inner x v v)
  have hlo : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) * |w.2| :=
    mul_nonneg (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) (abs_nonneg _)
  have heq : (N.scale * Real.sqrt (1 - N.epsilon) * |w.2|) ^ 2 =
      (1 - N.epsilon) * N.scale ^ 2 * w.2 ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hε.le, sq_abs]
    ring
  calc
    N.scale * Real.sqrt (1 - N.epsilon) * |w.2| =
        Real.sqrt ((N.scale * Real.sqrt (1 - N.epsilon) * |w.2|) ^ 2) :=
      (Real.sqrt_sq hlo).symm
    _ ≤ Real.sqrt (g.inner x v v) := Real.sqrt_le_sqrt (heq.trans_le hsq)


theorem axial_gradient_norm_le (D : LeviCivitaData g) {x : M} (hx : x ∈ N.carrier) :
    g.tangentNorm x (D.gradient (fun y => (N.coordinate_inverse y).2) x) ≤
      (N.scale * Real.sqrt (1 - N.epsilon))⁻¹ := by
  have hpos : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  apply (D.gradient_norm_le_iff _ x (inv_pos.mpr hpos).le).mpr
  intro v
  exact (le_inv_mul_iff₀ hpos).mpr (N.axial_mvfderiv_bound hx v)

end PoincareConjecture.EpsilonNeck
