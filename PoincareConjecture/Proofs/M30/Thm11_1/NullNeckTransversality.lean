import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30




theorem exists_neck_ricci_null_axial_bound :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ epsilon0 →
      ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
        D.ricci (N.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) = 0 →
        (49 / 50 : ℝ) * EvolvingRoundCylinderMetric 0 z v v ≤ v.2 ^ 2 := by
  obtain ⟨epsilon0, hepsilon0, hsmall, hcontrol⟩ :=
    EpsilonNeck.exists_ricci_quadratic_control.{u}
  refine ⟨epsilon0, hepsilon0, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hN z hz v hnull
  have h := (abs_le.mp (hcontrol N D hN z hz v)).1
  rw [hnull] at h
  linarith




theorem exists_neck_central_sphere_ricci_null_transversality :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ epsilon0 →
      let i : UnitTwoSphere → M := fun q => N.coordinate_map (q, 0)
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ i ∧
        IsCompact N.central_sphere ∧
        ∀ (q : UnitTwoSphere) (w : TangentSpace (𝓡 3) (i q)),
          w ≠ 0 → D.ricci (i q) w w = 0 →
          ¬ ∃ v : TangentSpace (𝓡 2) q,
            mfderiv (𝓡 2) (𝓡 3) i q v = w := by
  obtain ⟨epsilon0, hepsilon0, hsmall, hbound⟩ :=
    exists_neck_ricci_null_axial_bound.{u}
  refine ⟨epsilon0, hepsilon0, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hN
  dsimp only
  refine ⟨N.centralSphere_isSmoothEmbedding, N.isCompact_central_sphere, ?_⟩
  intro q w hw hnull
  rintro ⟨v, hv⟩
  have hz : (q, (0 : ℝ)) ∈ N.cylinderDomain :=
    ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
      inv_pos.mpr N.epsilon_pos⟩
  have hv0 : (v, (0 : ℝ)) ≠ (0 : RoundCylinderTangent (q, 0)) := by
    intro heq
    have hvzero : v = 0 := congrArg Prod.fst heq
    apply hw
    rw [hvzero] at hv
    simpa only [map_zero] using hv.symm
  have hnull' : D.ricci (N.coordinate_map (q, 0))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, 0) (v, 0))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, 0) (v, 0)) = 0 := by
    rw [← N.centralSphere_mfderiv q v, hv]
    exact hnull
  have haxial := hbound N D hN (q, 0) hz (v, 0) hnull'
  have hpos : 0 < EvolvingRoundCylinderMetric 0 (q, 0) (v, 0) (v, 0) := by
    rw [← roundCylinderProductMetric_inner (q, 0) (v, 0) (v, 0)]
    exact roundCylinderProductMetric.pos (q, 0) (v, 0) hv0
  simp only [zero_pow (by decide : 2 ≠ 0)] at haxial
  linarith

end PoincareConjecture.M30
