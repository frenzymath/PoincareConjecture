import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.FrontierNeck
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Singleton













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem openCylinderModel_tail_false_eq_region (N : EpsilonNeck g)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    N.openCylinderModel.tail false a =
      N.region (-N.epsilon⁻¹) ((2 * a - 1) * N.epsilon⁻¹) := by
  have hR : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  change N.openCylinderModel.coordinate '' (univ ×ˢ Ioo 0 a) = _
  ext x
  constructor
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    have htone : t < 1 := ht.2.trans ha.2
    have hdom : (2 * t - 1) * N.epsilon⁻¹ ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      constructor <;> nlinarith [mul_pos ht.1 hR, mul_pos (sub_pos.mpr htone) hR]
    change N.coordinate_map (q, (2 * t - 1) * N.epsilon⁻¹) ∈ _
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdom⟩, ?_⟩
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom⟩]
    exact ⟨hdom.1, by nlinarith [mul_pos (sub_pos.mpr ht.2) hR]⟩
  · intro hx
    have hlo := mul_lt_mul_of_pos_right hx.2.1 N.epsilon_pos
    have hhi := mul_lt_mul_of_pos_right hx.2.2 N.epsilon_pos
    simp only [neg_mul, mul_assoc, inv_mul_cancel₀ N.epsilon_pos.ne', mul_one] at hlo hhi
    let t := ((N.coordinate_inverse x).2 * N.epsilon + 1) / 2
    have ht : t ∈ Ioo 0 a := by dsimp [t]; constructor <;> linarith
    refine ⟨((N.coordinate_inverse x).1, t), ⟨mem_univ _, ht⟩, ?_⟩
    change N.coordinate_map ((N.coordinate_inverse x).1, (2 * t - 1) * N.epsilon⁻¹) = x
    have hnorm : (2 * t - 1) * N.epsilon⁻¹ = (N.coordinate_inverse x).2 := by
      dsimp [t]
      field_simp [N.epsilon_pos.ne']
      ring
    rw [hnorm, Prod.eta, N.coordinate_map_coordinate_inverse hx.1]


theorem openCylinderModel_tail_one_quarter (N : EpsilonNeck g) :
    N.openCylinderModel.tail false (1 / 4) = N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) := by
  rw [N.openCylinderModel_tail_false_eq_region (by norm_num : (1 / 4 : ℝ) ∈ Ioo 0 1)]
  congr 1
  ring

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate




theorem exists_frontier_neck_tail_inclusions_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∈ frontier C.carrier →
          ∃ (Q : EpsilonNeck g) (hQε : Q.epsilon ≤ 1 / 200),
            Q.SameUpToReversal P ∧ Q.IsSeparating ∧
            Disjoint C.closed_core Q.carrier ∧
            C.carrier ∩ (Q.tubeCertificate hQε).carrier = C.end_neck.carrier ∩ Q.carrier ∧
            (Q.tubeCertificate hQε).cylinder.tail false (1 / 4) ⊆ C.carrier ∧
            C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹ ⊆
              (Q.tubeCertificate hQε).carrier := by
  obtain ⟨ε₀, hε₀, hsmall, hoverlap⟩ := exists_frontier_neck_overlap_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hC hP hp
  obtain ⟨Q, hQ, hsep, hdis, hinter, hpos, hneg⟩ := hoverlap C P hC hP hp
  have hQeq : Q.epsilon = C.epsilon := hQ.epsilon_eq.trans hP
  have hQε : Q.epsilon ≤ 1 / 200 := hQeq.trans_le (hC.trans hsmall)
  refine ⟨Q, hQε, hQ, hsep, hdis, hinter, ?_, hpos⟩
  change Q.openCylinderModel.tail false (1 / 4) ⊆ C.carrier
  rw [Q.openCylinderModel_tail_one_quarter, hQeq]
  exact hneg.trans ((C.end_neck.region_subset_carrier _ _).trans C.end_neck_subset)

end PoincareConjecture.CapCertificate
