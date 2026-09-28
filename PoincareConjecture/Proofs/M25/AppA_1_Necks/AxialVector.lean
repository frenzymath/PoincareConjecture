import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxisControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

noncomputable def normalizedAxialVector (N : EpsilonNeck g) (x : M) : TangentSpace (𝓡 3) x :=
  N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    N.coordinate_map (N.coordinate_inverse x) (0, 1)

theorem normalizedEuclideanFrame_axial (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.normalizedEuclideanFrame q s (m25_roundCylinderEuclideanBasis 2) =
      N.normalizedAxialVector (N.coordinate_map (q, s)) := by
  let d : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) :=
    fun z => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z (0, 1)
  change N.scale⁻¹ • (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0
    (m25_roundCylinderEuclideanBasis 2) : EuclideanSpace ℝ (Fin 3)) =
      N.scale⁻¹ • d (N.coordinate_inverse (N.coordinate_map (q, s)))
  rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
  exact congrArg (fun v : EuclideanSpace ℝ (Fin 3) => N.scale⁻¹ • v)
    (N.euclideanParametrization_mfderiv_axial q hs)

theorem exists_intersecting_axial_control {α : ℝ} (hα : 0 < α) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ x : M, x ∈ N.carrier → x ∈ N'.carrier →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        g.tangentNorm x (N'.normalizedAxialVector x - σ • N.normalizedAxialVector x) < α := by
  obtain ⟨epsilon0, hpos, hcap, hcontrol⟩ := exists_normalized_axis_control.{u} hα
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' x hx hx'
  have hz := N.coordinate_inverse_mem x hx
  have hz' := N'.coordinate_inverse_mem x hx'
  have hp := N.coordinate_map_coordinate_inverse hx
  have hp' := N'.coordinate_map_coordinate_inverse hx'
  obtain ⟨σ, hσ, h⟩ := hcontrol N N' hN hN'
    (N.coordinate_inverse x).1 (N'.coordinate_inverse x).1 hz.2 hz'.2 (hp.trans hp'.symm)
  refine ⟨σ, hσ, ?_⟩
  let a : EuclideanSpace ℝ (Fin 3) := N.normalizedEuclideanFrame
    (N.coordinate_inverse x).1 (N.coordinate_inverse x).2 (m25_roundCylinderEuclideanBasis 2)
  let a' : EuclideanSpace ℝ (Fin 3) := N'.normalizedEuclideanFrame
    (N'.coordinate_inverse x).1 (N'.coordinate_inverse x).2 (m25_roundCylinderEuclideanBasis 2)
  have ha : a = (N.normalizedAxialVector x : EuclideanSpace ℝ (Fin 3)) :=
    (N.normalizedEuclideanFrame_axial (N.coordinate_inverse x).1 hz.2).trans
      (congrArg (fun y => (N.normalizedAxialVector y : EuclideanSpace ℝ (Fin 3))) hp)
  have ha' : a' = (N'.normalizedAxialVector x : EuclideanSpace ℝ (Fin 3)) :=
    (N'.normalizedEuclideanFrame_axial (N'.coordinate_inverse x).1 hz'.2).trans
      (congrArg (fun y => (N'.normalizedAxialVector y : EuclideanSpace ℝ (Fin 3))) hp')
  let Q : M → EuclideanSpace ℝ (Fin 3) → ℝ := fun y v => g.tangentNorm y v
  change Q (N.coordinate_map (N.coordinate_inverse x)) (a' - σ • a) < α at h
  rw [hp, ha, ha'] at h
  exact h

end PoincareConjecture.EpsilonNeck
