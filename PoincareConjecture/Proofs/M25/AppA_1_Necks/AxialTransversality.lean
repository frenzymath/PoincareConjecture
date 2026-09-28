import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialVector
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Directional












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem normalizedAxialVector_axial_mvfderiv (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x
      (N.normalizedAxialVector x) = 1 := by
  have h := N.axial_mvfderiv_coordinate_tangent (N.coordinate_inverse_mem x hx) (0, 1)
  let L : M → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    fun y => mvfderiv (𝓡 3) (fun z => (N.coordinate_inverse z).2) y
  let a : EuclideanSpace ℝ (Fin 3) := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    N.coordinate_map (N.coordinate_inverse x) (0, 1)
  change L (N.coordinate_map (N.coordinate_inverse x)) a = 1 at h
  rw [N.coordinate_map_coordinate_inverse hx] at h
  change N.scale * L x (N.scale⁻¹ • a) = 1
  rw [map_smul, smul_eq_mul, h, mul_one, mul_inv_cancel₀ N.scale_pos.ne']




theorem exists_intersecting_axial_derivative_control {η : ℝ} (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ x : M, x ∈ N.carrier → x ∈ N'.carrier →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        |1 - σ * N'.scale * mvfderiv (𝓡 3)
          (fun y => (N'.coordinate_inverse y).2) x (N.normalizedAxialVector x)| < η := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ :=
    exists_intersecting_axial_control.{u} (half_pos hη)
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' x hx hx'
  obtain ⟨σ, hσ, hclose⟩ := hcontrol N N' hN hN' x hx hx'
  refine ⟨σ, hσ, ?_⟩
  let L := mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x
  let w := N'.normalizedAxialVector x - σ • N.normalizedAxialVector x
  have hbound := (N'.axial_mvfderiv_bound hx' w).trans_lt hclose
  have heq : N'.scale * L w = 1 - σ * N'.scale * L (N.normalizedAxialVector x) := by
    dsimp only [w]
    rw [map_sub, map_smul, smul_eq_mul, mul_sub]
    rw [show N'.scale * L (N'.normalizedAxialVector x) = 1 from
      N'.normalizedAxialVector_axial_mvfderiv hx']
    ring
  have habs : N'.scale * |L w| =
      |1 - σ * N'.scale * L (N.normalizedAxialVector x)| := by
    calc
      _ = |N'.scale * L w| := by rw [abs_mul, abs_of_pos N'.scale_pos]
      _ = _ := congrArg abs heq
  have hscaled : Real.sqrt (1 - N'.epsilon) *
      |1 - σ * N'.scale * L (N.normalizedAxialVector x)| < η / 2 := by
    calc
      _ = N'.scale * Real.sqrt (1 - N'.epsilon) * |L w| := by rw [← habs]; ring
      _ < η / 2 := hbound
  have hhalf : (1 : ℝ) / 2 < Real.sqrt (1 - N'.epsilon) :=
    (Real.lt_sqrt (by norm_num)).mpr (by linarith [N'.epsilon_lt_half])
  have hmul := mul_le_mul_of_nonneg_right hhalf.le
    (abs_nonneg (1 - σ * N'.scale * L (N.normalizedAxialVector x)))
  change |1 - σ * N'.scale * L (N.normalizedAxialVector x)| < η
  linarith




theorem exists_intersecting_axial_transversality :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ x : M, x ∈ N.carrier → x ∈ N'.carrier →
        mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x
          (N.normalizedAxialVector x) ≠ 0 ∧
        mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x
          (N'.normalizedAxialVector x) ≠ 0 := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ :=
    exists_intersecting_axial_derivative_control.{u} (η := 1 / 2) (by norm_num)
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' x hx hx'
  constructor
  · obtain ⟨σ, _, h⟩ := hcontrol N N' hN hN' x hx hx'
    intro hz
    norm_num [hz] at h
  · obtain ⟨σ, _, h⟩ := hcontrol N' N hN' hN x hx' hx
    intro hz
    norm_num [hz] at h

end PoincareConjecture.EpsilonNeck
