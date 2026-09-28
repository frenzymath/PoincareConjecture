import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem standard_initial_neck_birth_native_upper
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z
      (Icc (-v * (G.connection v).scalarCurvature z) 0))
    (hsmall : gamma ≤ 1 / 1200)
    (hdisjoint : Disjoint N.patch.carrier
      {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
    (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)
    (a : RoundCylinderSpace) (ha : a.2 ∈ Ioo (-gamma⁻¹) gamma⁻¹)
    (w : RoundCylinderTangent a) :
    roundCylinderPullback g0.metric N.patch.coordinate a w w ≤
      (51 / 50 : ℝ) ^ 2 * EvolvingRoundCylinderMetric 0 a w w := by
  let p := M35.cylinderCoordinateEquiv.symm (0, a.2)
  have hp : M35.cylinderCoordinateEquiv p = (0, a.2) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, a.2)
  have hchart : M35.cylinderChart a.1 p = a := by
    change ((chartAt (EuclideanSpace ℝ (Fin 2)) a.1).symm
      (M35.cylinderCoordinateEquiv p).1, (M35.cylinderCoordinateEquiv p).2) = a
    rw [hp]
    apply Prod.ext
    · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) a.1).left_inv
        (mem_chart_source (EuclideanSpace ℝ (Fin 2)) a.1)
      simpa only [M35.sphere_chart_center] using h
    · rfl
  let D := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (M35.cylinderChart a.1) p
  obtain ⟨e, he⟩ := M35.cylinderChart_mfderiv_invertible a.1 p
  let b : EuclideanSpace ℝ (Fin 3) := e.symm w
  have hb : D b = w := by
    change mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (M35.cylinderChart a.1) p (e.symm w) = w
    rw [← he]
    exact e.apply_symm_apply w
  have hN : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      N.patch.coordinate (M35.cylinderChart a.1 p) := by
    apply (N.patch.coordinate_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ?_)).mdifferentiableAt (by simp)
    rw [hchart]
    exact ⟨mem_univ _, ha⟩
  have hchain := mfderiv_comp p hN
    ((M35.cylinderChart_contMDiff a.1 p).mdifferentiableAt (by simp))
  have hmodel : EvolvingRoundCylinderMetric 0 (M35.cylinderChart a.1 p) (D b) (D b) =
      M35.cylinderEuclideanCoefficients 0 p b b := by
    dsimp only [D]
    rw [M35.mfderiv_cylinderChart]
    change 2 * (1 - (0 : ℝ)) *
        inner ℝ
          (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
            ((chartAt (EuclideanSpace ℝ (Fin 2)) a.1).symm
              (M35.cylinderCoordinateEquiv p).1)
            (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) a.1).symm
              (M35.cylinderCoordinateEquiv p).1 (M35.cylinderCoordinateEquiv b).1))
          (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
            ((chartAt (EuclideanSpace ℝ (Fin 2)) a.1).symm
              (M35.cylinderCoordinateEquiv p).1)
            (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) a.1).symm
              (M35.cylinderCoordinateEquiv p).1 (M35.cylinderCoordinateEquiv b).1)) +
        (M35.cylinderCoordinateEquiv b).2 * (M35.cylinderCoordinateEquiv b).2 = _
    rw [M35.sphere_chart_pullback_inner_at, M35.cylinderEuclideanCoefficients_apply]
    ring
  have hbound := (standard_initial_neck_birth_pullback_bounds N hsmall hdisjoint hshort
    a.1 a.2 ha b).2
  change g0.metric.inner (N.patch.coordinate (M35.cylinderChart a.1 p))
      (mfderiv (𝓡 3) (𝓡 3) (N.patch.coordinate ∘ M35.cylinderChart a.1) p b)
      (mfderiv (𝓡 3) (𝓡 3) (N.patch.coordinate ∘ M35.cylinderChart a.1) p b) ≤
        (51 / 50 : ℝ) ^ 2 * M35.cylinderEuclideanCoefficients 0 p b b at hbound
  rw [hchain] at hbound
  change roundCylinderPullback g0.metric N.patch.coordinate
    (M35.cylinderChart a.1 p) (D b) (D b) ≤
      (51 / 50 : ℝ) ^ 2 * M35.cylinderEuclideanCoefficients 0 p b b at hbound
  rw [← hmodel, hb, hchart] at hbound
  exact hbound

end PoincareConjecture.M47
