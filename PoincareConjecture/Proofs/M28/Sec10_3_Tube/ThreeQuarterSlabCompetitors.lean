import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompetitors
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem intrinsicEDist_lt_three_quarter_ceiling (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ (1 / 10000 : ℝ)) {p x : M}
    (hp : p ∈ N.central_sphere) (hx : x ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4) :
    intrinsicEDist g N.carrier p x <
      ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * N.epsilon⁻¹) := by
  have hApos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hA : (10000 : ℝ) ≤ N.epsilon⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right hsmall hApos.le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at hh
    linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1001 / 1000 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hconstant : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
    have hs : Real.sqrt 2 ≤ (2 : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hh := mul_le_mul_of_nonneg_right hs
      (show 0 ≤ Real.pi + 1 by linarith [Real.pi_pos])
    nlinarith only [hh, Real.pi_lt_four]
  have hfactor : Real.sqrt (1 + N.epsilon) *
      (|(N.coordinate_inverse x).2| + Real.sqrt 2 * (Real.pi + 1)) <
        (151 / 200 : ℝ) * N.epsilon⁻¹ := by
    apply (mul_le_mul_of_nonneg_right hroot (by positivity)).trans_lt
    nlinarith only [hheight, hconstant, hA]
  have hp0 := (N.mem_central_sphere_iff_of_mem_carrier (N.central_sphere_subset hp)).mp hp
  have hd := N.intrinsicEDist_le_axial_add (N.central_sphere_subset hp) hx
  rw [hp0, sub_zero] at hd
  apply hd.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (mul_pos (by norm_num) N.scale_pos) hApos)).mpr
  have hh := mul_lt_mul_of_pos_left hfactor N.scale_pos
  nlinarith only [hh]

theorem exists_three_quarter_slab_competitor (N : EpsilonNeck g)
    (hsmall : N.epsilon ≤ (1 / 10000 : ℝ)) {p x : M}
    (hp : p ∈ N.central_sphere) (hx : x ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x).2| ≤ 3 * N.epsilon⁻¹ / 4) :
    ∃ gamma : ℝ → M, gamma 0 = p ∧ gamma 1 = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc (0 : ℝ) 1) ∧
      MapsTo gamma (Icc (0 : ℝ) 1) N.carrier ∧
      g.pathELength gamma 0 1 <
        ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * N.epsilon⁻¹) :=
  M28.exists_intrinsic_competitor g
    (N.intrinsicEDist_lt_three_quarter_ceiling hsmall hp hx hheight)

end PoincareConjecture.EpsilonNeck
