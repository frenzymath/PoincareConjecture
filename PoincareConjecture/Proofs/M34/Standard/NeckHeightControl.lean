import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparison
import PoincareConjecture.Proofs.M34.Standard.PathLengthComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem coordinate_map_inverse_eq {x : M} (hx : x ∈ N.carrier) :
    N.coordinate_map (N.coordinate_inverse x) = x := by
  have h := congrArg (fun z : N.carrier => (z : M)) (N.coordinate_inverse_right x hx)
  rw [N.coordinate_map_eq] at h
  exact h




theorem coordinate_map_inverse_mfderiv {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) = v := by
  have hi := ((N.coordinate_inverse_smooth x hx).contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hm := ((N.coordinate_map_smooth _ (N.coordinate_inverse_mem x hx)).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds (N.coordinate_inverse_mem x hx))).mdifferentiableAt
      (by simp)
  have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.coordinate_map_inverse_eq hy
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x hm hi, mfderiv_id] at hd
  exact congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hd




theorem coordinate_inverse_axial_le_tangentNorm {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    |(mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v).2| ≤
      (2 / N.scale) * g.tangentNorm x v := by
  let z := N.coordinate_inverse x
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem x hx).2
  have hcomp := (N.pullback_inner_comparison hz w).1
  have hmap : N.coordinate_map z = x := N.coordinate_map_inverse_eq hx
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w = v :=
    N.coordinate_map_inverse_mfderiv hx v
  have hpull : roundCylinderPullback g N.coordinate_map z w w = g.inner x v v := by
    unfold roundCylinderPullback
    rw [hd]
    change g.inner (N.coordinate_map z) v v = _
    rw [hmap]
  have haxial : w.2 ^ 2 ≤ EvolvingRoundCylinderMetric 0 z w w := by
    unfold EvolvingRoundCylinderMetric
    let a : EuclideanSpace ℝ (Fin 3) := mfderiv (𝓡 2) (𝓡 3)
      (fun q : UnitTwoSphere => (q : EuclideanSpace ℝ (Fin 3))) z.1 w.1
    have hpos : 0 ≤ inner ℝ a a := real_inner_self_nonneg
    nlinarith
  have hinner : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hnorm : g.tangentNorm x v ^ 2 = g.inner x v v := Real.sq_sqrt hinner
  have hnormpos : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
  have hscale : 0 < N.scale := N.scale_pos
  have hproduct : 0 ≤ (2 / N.scale) * g.tangentNorm x v := by positivity
  have hsq : |w.2| ^ 2 ≤ ((2 / N.scale) * g.tangentNorm x v) ^ 2 := by
    rw [hpull] at hcomp
    rw [sq_abs, mul_pow, hnorm]
    have heq : (2 / N.scale) ^ 2 = 4 * N.scale⁻¹ ^ 2 := by ring
    rw [heq]
    nlinarith [mul_nonneg (sq_nonneg N.scale⁻¹) hinner]
  exact (sq_le_sq₀ (abs_nonneg _) hproduct).mp hsq

end PoincareConjecture.EpsilonNeck
