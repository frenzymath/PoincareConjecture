import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Proper
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.FiberSign

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem overlapBarrierMap_injective_of_axial_strictMono (N Q : EpsilonNeck g)
    (hmono : ∀ q : UnitTwoSphere,
      StrictMonoOn (fun t : ℝ => (N.coordinate_inverse (Q.coordinate_map (q, t))).2)
        {t | t ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ ∧ Q.coordinate_map (q, t) ∈ N.carrier}) :
    Function.Injective (N.overlapBarrierMap Q) := by
  have hstrict (x y : ↥(N.carrier ∩ Q.carrier))
      (hang : (Q.coordinate_inverse x).1 = (Q.coordinate_inverse y).1)
      (hlt : (Q.coordinate_inverse x).2 < (Q.coordinate_inverse y).2) :
      N.overlapBarrier Q x < N.overlapBarrier Q y := by
    have hx := Q.coordinate_inverse_mem x x.property.2
    have hy := Q.coordinate_inverse_mem y y.property.2
    have hnx := N.coordinate_inverse_mem x x.property.1
    have hny := N.coordinate_inverse_mem y y.property.1
    have hfx : Q.coordinate_map ((Q.coordinate_inverse x).1, (Q.coordinate_inverse x).2) = x :=
      Q.coordinate_map_coordinate_inverse x.property.2
    have hfy : Q.coordinate_map ((Q.coordinate_inverse x).1, (Q.coordinate_inverse y).2) = y := by
      rw [hang]
      exact Q.coordinate_map_coordinate_inverse y.property.2
    have hn := hmono (Q.coordinate_inverse x).1
      ⟨hx.2, by rw [hfx]; exact x.property.1⟩
      ⟨hy.2, by rw [hfy]; exact y.property.1⟩ hlt
    dsimp only at hn
    rw [hfx, hfy] at hn
    have hleft : (N.epsilon⁻¹ - (N.coordinate_inverse x).2)⁻¹ <
        (N.epsilon⁻¹ - (N.coordinate_inverse y).2)⁻¹ :=
      inv_strictAnti₀ (by linarith [hny.2.2]) (by linarith)
    have hright : (Q.epsilon⁻¹ + (Q.coordinate_inverse y).2)⁻¹ <
        (Q.epsilon⁻¹ + (Q.coordinate_inverse x).2)⁻¹ :=
      inv_strictAnti₀ (by linarith [hx.2.1]) (by linarith)
    dsimp [overlapBarrier]
    linarith
  intro x y hxy
  have hang : (Q.coordinate_inverse x).1 = (Q.coordinate_inverse y).1 := by
    simpa only [overlapBarrierMap] using congrArg Prod.fst hxy
  have hheight : N.overlapBarrier Q x = N.overlapBarrier Q y := by
    simpa only [overlapBarrierMap] using congrArg Prod.snd hxy
  have haxis : (Q.coordinate_inverse x).2 = (Q.coordinate_inverse y).2 := by
    rcases lt_trichotomy (Q.coordinate_inverse x).2 (Q.coordinate_inverse y).2 with hlt | heq | hgt
    · exact False.elim (ne_of_lt (hstrict x y hang hlt) hheight)
    · exact heq
    · exact False.elim (ne_of_lt (hstrict y x hang.symm hgt) hheight.symm)
  apply Subtype.ext
  rw [← Q.coordinate_map_coordinate_inverse x.property.2,
    ← Q.coordinate_map_coordinate_inverse y.property.2, Prod.ext hang haxis]

theorem exists_overlapBarrierMap_injective_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N Q : EpsilonNeck g), N.epsilon ≤ ε₀ → Q.epsilon ≤ ε₀ →
          N.carrier ∩ Q.carrier ⊆
            N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
              Q.region (-Q.epsilon⁻¹) (Q.epsilon⁻¹ / 2) →
          Function.Injective (N.overlapBarrierMap Q) := by
  obtain ⟨ε₁, hε₁, hsmall, hconnected⟩ := exists_axial_overlap_fiber_preconnected_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hderiv⟩ := exists_axial_overlap_fiber_positive_deriv_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N Q hN hQ hoverlap
  apply N.overlapBarrierMap_injective_of_axial_strictMono Q
  intro q
  have hS := hconnected N Q (hN.trans (min_le_left _ _))
    (hQ.trans (min_le_left _ _)) hoverlap q
  apply strictMonoOn_of_deriv_pos hS.ordConnected.convex
  · intro t ht
    exact (N.transition_axis_contDiffAt Q q ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    have hx := interior_subset ht
    have hd := (hderiv N Q (hN.trans (min_le_right _ _))
      (hQ.trans (min_le_right _ _)) hoverlap q t hx.1 hx.2).1
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 0.9) hd

end PoincareConjecture.EpsilonNeck
