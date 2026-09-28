import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.AxialContraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Comparison



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

local notation "Cyl" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem tangentNorm_axial_compression_le (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 200)
    (J : Diffeomorph Cyl Cyl RoundCylinderSpace RoundCylinderSpace ∞)
    (a : ℝ) {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (hJ : ∀ p : RoundCylinderSpace,
      J p = (p.1, p.2 + d * Real.smoothTransition ((p.2 - a) / δ)))
    {x : M} (hx : x ∈ N.carrier)
    (hdom : J.symm (N.coordinate_inverse x) ∈ N.cylinderDomain)
    (v : TangentSpace (𝓡 3) x) :
    g.tangentNorm ((N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse) x)
        (mfderiv (𝓡 3) (𝓡 3)
          (N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse) x v) ≤
      (11 / 10 : ℝ) * g.tangentNorm x v := by
  let z := N.coordinate_inverse x
  let w := mfderiv (𝓡 3) Cyl N.coordinate_inverse x v
  have hz := N.coordinate_inverse_mem x hx
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hdom)).mdifferentiableAt (by simp)
  have hJd := J.symm.contMDiff.mdifferentiable (by simp) z
  have hcompose := mfderiv_comp x hm (hJd.comp x hi)
  rw [mfderiv_comp x hJd hi] at hcompose
  have hback : mfderiv Cyl (𝓡 3) N.coordinate_map z w = v := by
    have hcomp := mfderiv_comp x
      ((N.coordinate_map_smooth.contMDiffAt
        (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp)) hi
    have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
      filter_upwards [N.carrier_open.mem_nhds hx] with y hy
      exact N.coordinate_map_coordinate_inverse hy
    rw [heq.mfderiv_eq, mfderiv_id] at hcomp
    exact (congrArg (fun L => L v) hcomp).symm
  have hlower := (N.pullback_metric_bounds hz.2 w).1
  change (1 - N.epsilon) * N.scale ^ 2 * EvolvingRoundCylinderMetric 0 z w w ≤
    g.inner (N.coordinate_map z)
      (mfderiv Cyl (𝓡 3) N.coordinate_map z w)
      (mfderiv Cyl (𝓡 3) N.coordinate_map z w) at hlower
  rw [hback, N.coordinate_map_coordinate_inverse hx] at hlower
  have hupper := (N.pullback_metric_bounds hdom.2
    (mfderiv Cyl Cyl J.symm z w)).2
  have hcontract := CylinderGluing.inverse_axial_expansion_round_metric_le
    J a hδ hd hJ z w
  have hmodel : 0 ≤ EvolvingRoundCylinderMetric 0 z w w := by
    dsimp [EvolvingRoundCylinderMetric]
    exact add_nonneg (mul_nonneg (by norm_num) (real_inner_self_nonneg)) (mul_self_nonneg _)
  have hfactor : 0 ≤ (1 + N.epsilon) * N.scale ^ 2 := by
    have he := N.epsilon_pos
    positivity
  have hcoef : (1 + N.epsilon) ≤ (11 / 10 : ℝ) ^ 2 * (1 - N.epsilon) := by
    nlinarith
  have hquad :
      g.inner ((N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse) x)
        (mfderiv (𝓡 3) (𝓡 3) (N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse) x v)
        (mfderiv (𝓡 3) (𝓡 3) (N.coordinate_map ∘ J.symm ∘ N.coordinate_inverse) x v) ≤
      (11 / 10 : ℝ) ^ 2 * g.inner x v v := by
    rw [hcompose]
    change roundCylinderPullback g N.coordinate_map (J.symm z)
        (mfderiv Cyl Cyl J.symm z w) (mfderiv Cyl Cyl J.symm z w) ≤ _
    calc
      _ ≤ (1 + N.epsilon) * N.scale ^ 2 * EvolvingRoundCylinderMetric 0 z w w :=
        hupper.trans (mul_le_mul_of_nonneg_left hcontract hfactor)
      _ ≤ (11 / 10 : ℝ) ^ 2 *
          ((1 - N.epsilon) * N.scale ^ 2 * EvolvingRoundCylinderMetric 0 z w w) := by
        have hh := mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (sq_nonneg N.scale) hmodel)
        nlinarith
      _ ≤ (11 / 10 : ℝ) ^ 2 * g.inner x v v :=
        mul_le_mul_of_nonneg_left hlower (sq_nonneg _)
  have hnorm := Real.sqrt_le_sqrt hquad
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 11 / 10)] at hnorm
  exact hnorm

end PoincareConjecture.EpsilonNeck
