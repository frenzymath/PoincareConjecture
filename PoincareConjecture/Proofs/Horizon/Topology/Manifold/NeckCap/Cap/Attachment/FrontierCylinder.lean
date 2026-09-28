import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.Tails
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.SuccessorThreeQuarter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Regions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_frontier_neck_capTubeAttachment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∈ frontier C.carrier →
          ∃ (Q : EpsilonNeck g) (hQε : Q.epsilon ≤ 1 / 200),
            Q.SameUpToReversal P ∧ Q.IsSeparating ∧
              Nonempty (CapTubeAttachment C (Q.tubeCertificate hQε) false) := by
  obtain ⟨ε₁, hε₁, hsmall, hseparate⟩ := exists_end_neck_separating_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hfrontier⟩ := exists_frontier_carrier_subset_closure_positive_end.{u}
  obtain ⟨ε₃, hε₃, -, hbalanced⟩ := EpsilonNeck.exists_frontier_reversal_balanced_overlap.{u}
  obtain ⟨ε₄, hε₄, -, havoid⟩ := exists_frontier_neck_disjoint_closed_core_threshold.{u}
  obtain ⟨ε₅, hε₅, -, hcapture⟩ :=
    EpsilonNeck.exists_positive_quarter_subset_frontier_neck_inner_slab_threshold.{u}
  obtain ⟨ε₆, hε₆, -, hcylinder⟩ := EpsilonNeck.exists_full_overlap_cylinder_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ (min ε₄ (min ε₅ ε₆)))),
    lt_min hε₁ (lt_min hε₂ (lt_min hε₃ (lt_min hε₄ (lt_min hε₅ hε₆)))),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hε heq hp
  have h₁ := hε.trans (min_le_left _ _)
  have hrest := hε.trans (min_le_right _ _)
  have h₂ := hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have h₃ := hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have h₄ := hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have h₅ := hrest.trans (min_le_left _ _)
  have h₆ := hrest.trans (min_le_right _ _)
  have hNsep := hseparate C h₁
  have hcontact : P.center ∈ closure
      (C.end_neck.region (C.end_neck.epsilon⁻¹ / 2) C.end_neck.epsilon⁻¹) := by
    simpa only [C.end_neck_epsilon] using hfrontier C h₂ hp
  have hout : P.center ∉ C.end_neck.carrier :=
    fun h => (C.carrier_open.frontier_eq ▸ hp).2 (C.end_neck_subset h)
  obtain ⟨Q, hsame, hpositive, hnegative, hthree, hmargin, hQsep⟩ :=
    hbalanced C.end_neck P hNsep (C.end_neck_epsilon.trans_le h₃)
      (heq.trans C.end_neck_epsilon.symm) hcontact hout
  have hQN : Q.epsilon = C.end_neck.epsilon :=
    hsame.epsilon_eq.trans (heq.trans C.end_neck_epsilon.symm)
  have hQC : Q.epsilon = C.epsilon := hQN.trans C.end_neck_epsilon
  have hQε : Q.epsilon ≤ 1 / 200 := hQC.trans_le (h₁.trans hsmall)
  have hQcontact : Q.center ∈ closure
      (C.end_neck.region (C.end_neck.epsilon⁻¹ / 2) C.end_neck.epsilon⁻¹) := by
    rwa [hsame.center_eq]
  have hinner := hcapture C.end_neck Q (C.end_neck_epsilon.trans_le h₅) hQN hQcontact
  rw [hQN] at hinner
  obtain ⟨model⟩ := hcylinder C.end_neck Q (C.end_neck_epsilon.trans_le h₆)
    hQN hthree hinner hmargin
  have hdisj : Disjoint C.closed_core Q.carrier := by
    rw [hsame.carrier_eq]
    exact havoid C P h₄ heq hp
  have hinter : C.carrier ∩ Q.carrier = C.end_neck.carrier ∩ Q.carrier := by
    rw [C.carrier_eq_closed_core_union_end, union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp hdisj, empty_union]
  have hoverlap : OpenCylinderModel (C.carrier ∩ (Q.tubeCertificate hQε).carrier) := by
    change OpenCylinderModel (C.carrier ∩ Q.carrier)
    rw [hinter]
    exact model
  refine ⟨Q, hQε, hsame, hQsep, ⟨⟨hoverlap, ?_, ?_⟩⟩⟩
  · refine ⟨1 / 4, by norm_num, ?_⟩
    change Q.openCylinderModel.tail false (1 / 4) ⊆ C.carrier
    rw [Q.openCylinderModel_tail_one_quarter, hQN]
    exact hnegative.trans C.end_neck_subset
  · have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
    refine ⟨C.epsilon⁻¹ / 2, ⟨by linarith, by linarith⟩, ?_⟩
    change C.end_neck.region (C.epsilon⁻¹ / 2) C.epsilon⁻¹ ⊆ Q.carrier
    simpa only [C.end_neck_epsilon] using hpositive

theorem exists_frontier_neck_cappedTube_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C : CapCertificate g) (P : EpsilonNeck g), C.epsilon ≤ ε₀ →
          P.epsilon = C.epsilon → P.center ∈ frontier C.carrier →
          ∃ A : CappedTubeCertificate g, A.cap = C ∧
            A.tube.epsilon = C.epsilon ∧ A.tube.carrier = P.carrier ∧
            A.carrier = C.carrier ∪ P.carrier ∧ A.attachment_side = false := by
  obtain ⟨ε₀, hε₀, hsmall, hattach⟩ := exists_frontier_neck_capTubeAttachment_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C P hε heq hp
  obtain ⟨Q, hQε, hsame, -, ⟨attachment⟩⟩ := hattach C P hε heq hp
  let tube : EpsilonTubeCertificate g ∅ :=
    { Q.tubeCertificate hQε with contains_X := empty_subset _ }
  have attachment' : CapTubeAttachment C tube false :=
    ⟨attachment.overlap_model, attachment.tube_tail, attachment.cap_tail⟩
  have hmeet : (C.carrier ∩ tube.carrier).Nonempty :=
    attachment.overlap_model.isConnected_carrier.nonempty
  let A : CappedTubeCertificate g :=
    { carrier := C.carrier ∪ tube.carrier
      cap := C
      tube := tube
      cap_subset := subset_union_left
      tube_subset := subset_union_right
      carrier_eq_union := rfl
      connected := C.isConnected_carrier.union hmeet tube.cylinder.isConnected_carrier
      attachment_side := false
      attachment := attachment' }
  exact ⟨A, rfl, hsame.epsilon_eq.trans heq, hsame.carrier_eq,
    congrArg (C.carrier ∪ ·) hsame.carrier_eq, rfl⟩

end PoincareConjecture.CapCertificate
