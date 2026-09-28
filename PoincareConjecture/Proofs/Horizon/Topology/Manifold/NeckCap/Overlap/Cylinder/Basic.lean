import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Injective
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Smooth
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Diffeomorph













set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_full_overlap_cylinder_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N Q : EpsilonNeck g), N.epsilon ≤ ε₀ → Q.epsilon = N.epsilon →
          N.carrier ∩ Q.carrier ⊆
            N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
              Q.region (-N.epsilon⁻¹) (N.epsilon⁻¹ / 2) →
          N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆
            Q.coordinate_map '' (univ ×ˢ
              Icc (-(3 / 4 : ℝ) * N.epsilon⁻¹) ((3 / 4 : ℝ) * N.epsilon⁻¹)) →
          Q.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
            N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) →
          Nonempty (OpenCylinderModel (N.carrier ∩ Q.carrier)) := by
  obtain ⟨ε₁, hε₁, hsmall, hinjective⟩ := exists_overlapBarrierMap_injective_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hderiv⟩ := exists_axial_overlap_fiber_positive_deriv_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N Q hN heq hoverlap hpositive hnegative
  have hdir : N.carrier ∩ Q.carrier ⊆
      N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
        Q.region (-Q.epsilon⁻¹) (Q.epsilon⁻¹ / 2) := by
    simpa only [heq] using hoverlap
  let U : Opens M := ⟨N.carrier ∩ Q.carrier, N.carrier_open.inter Q.carrier_open⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ↥(N.carrier ∩ Q.carrier) :=
    (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) U)
  have hlocal : IsLocalDiffeomorph (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (N.overlapBarrierMap Q : U → RoundCylinderSpace) := by
    apply N.overlapBarrierMap_isLocalDiffeomorph Q
    intro z hz
    have hd := (hderiv N Q (hN.trans (min_le_right _ _))
      (heq.trans_le (hN.trans (min_le_right _ _))) hdir z.1 z.2 hz.1.2 hz.2).1
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 0.9) hd
  have hproper := N.isProperMap_overlapBarrierMap Q heq hoverlap hpositive hnegative
  have hinj := hinjective N Q (hN.trans (min_le_left _ _))
    (heq.trans_le (hN.trans (min_le_left _ _))) hdir
  let q₀ := (Q.coordinate_inverse Q.center).1
  have hR : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have ht : (-(3 / 4 : ℝ) * N.epsilon⁻¹) ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ := by
    rw [heq]
    constructor <;> linarith
  have hxQ := Q.coordinate_map_mem (show (q₀, -(3 / 4 : ℝ) * N.epsilon⁻¹) ∈
    Q.cylinderDomain from ⟨mem_univ _, ht⟩)
  have hxN : Q.coordinate_map (q₀, -(3 / 4 : ℝ) * N.epsilon⁻¹) ∈ N.carrier := by
    apply (hnegative ?_).1
    refine ⟨hxQ, ?_⟩
    rw [Q.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩]
    constructor <;> linarith
  let x₀ : U := ⟨Q.coordinate_map (q₀, -(3 / 4 : ℝ) * N.epsilon⁻¹), hxN, hxQ⟩
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have hclopen : IsClopen (range (N.overlapBarrierMap Q)) :=
    ⟨hproper.isClosedMap.isClosed_range, hlocal.isOpen_range⟩
  have hsurj : Function.Surjective (N.overlapBarrierMap Q) :=
    range_eq_univ.mp (hclopen.eq_univ ⟨N.overlapBarrierMap Q x₀, mem_range_self x₀⟩)
  let F := hlocal.diffeomorphOfBijective ⟨hinj, hsurj⟩
  obtain ⟨E, -⟩ := N.exists_unit_to_real_cylinder
  exact ⟨OpenCylinderModel.ofDiffeomorph U (E.trans F.symm) q₀⟩

end PoincareConjecture.EpsilonNeck
