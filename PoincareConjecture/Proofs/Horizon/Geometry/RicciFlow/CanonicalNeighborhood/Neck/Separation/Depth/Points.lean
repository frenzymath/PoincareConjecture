import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Depth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.DepthProfile










noncomputable section
set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem half_neck_depth_lower_bound (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) {σ : ℝ} (hσ : |σ| = 1)
    (haxis : (N.coordinate_inverse x).2 = σ / (2 * N.epsilon))
    {y : M} (hy : y ∈ N.central_sphere) :
    N.scale * Real.sqrt (1 - N.epsilon) / (neckDepthConstant * N.epsilon) ≤
      (g.edist x y).toReal := by
  have hC : 0 < neckDepthConstant := neckDepthConstant_pos
  have hε := N.epsilon_pos
  have hinv := inv_pos.mpr hε
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  obtain ⟨φ, hφ, hsupp, hzero, hone, hderiv⟩ :=
    exists_half_neck_profile.choose_spec.2 N.epsilon hε σ hσ
  have ha : -N.epsilon⁻¹ < -(3 / 4) * N.epsilon⁻¹ := by linarith
  have hb : (3 / 4) * N.epsilon⁻¹ < N.epsilon⁻¹ := by linarith
  have hy' := (N.mem_central_sphere_iff y).mp hy
  have hxone : N.axialCutoff φ x = 1 := by
    rw [N.axialCutoff_eq_of_mem φ hx, haxis]
    exact hone
  have hyzero : N.axialCutoff φ y = 0 := by
    rw [N.axialCutoff_eq_of_mem φ hy'.1, hy'.2, hzero]
  have hdist := N.abs_axialCutoff_sub_le ha hb hφ hsupp (mul_pos hC hε) hderiv x y
  rw [hxone, hyzero, sub_zero, abs_one] at hdist
  apply (div_le_iff₀ (mul_pos hC hε)).mpr
  have h := (le_div_iff₀ hfactor).mp (show 1 ≤
      (neckDepthConstant * N.epsilon * (g.edist x y).toReal) /
        (N.scale * Real.sqrt (1 - N.epsilon)) by
    simpa only [div_mul_eq_mul_div] using hdist)
  nlinarith

theorem exists_deep_point_of_epsilon_le (N : EpsilonNeck g)
    (hN : N.epsilon ≤ neckSeparationThreshold) (σ : ℝ) (hσ : |σ| = 1) :
      ∃ x ∈ N.carrier,
        (N.coordinate_inverse x).2 = σ / (2 * N.epsilon) ∧
        ∀ y ∈ N.central_sphere, (2 * Real.pi) * N.scale < (g.edist x y).toReal := by
  let C := neckDepthConstant
  have hC : 0 < C := neckDepthConstant_pos
  have hε := N.epsilon_pos
  have hs := N.scale_pos
  have hinv := inv_pos.mpr hε
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have hεbound : N.epsilon * (8 * Real.pi * C) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (hN.trans (min_le_right _ _))
  have hdepth : (2 * Real.pi) * N.scale <
      N.scale * Real.sqrt (1 - N.epsilon) / (C * N.epsilon) := by
    apply (lt_div_iff₀ (mul_pos hC hε)).mpr
    have hnum : C * N.epsilon * (2 * Real.pi) ≤ 1 / 4 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hnum hs.le
    have hr := mul_le_mul_of_nonneg_left hroot hs.le
    nlinarith
  let q : UnitTwoSphere := (N.coordinate_inverse N.center).1
  let t := σ / (2 * N.epsilon)
  have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have habs : |t| = N.epsilon⁻¹ / 2 := by
      dsimp [t]
      rw [abs_div, hσ, abs_of_pos (by positivity)]
      field_simp
    exact abs_lt.mp (by rw [habs]; linarith)
  let x := N.coordinate_map (q, t)
  have hx : x ∈ N.carrier := N.coordinate_map_mem ⟨mem_univ _, ht⟩
  have hcoord : N.coordinate_inverse x = (q, t) :=
    N.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩
  refine ⟨x, hx, congrArg Prod.snd hcoord, ?_⟩
  intro y hy
  exact hdepth.trans_le (N.half_neck_depth_lower_bound hx hσ (congrArg Prod.snd hcoord) hy)

end PoincareConjecture.EpsilonNeck
