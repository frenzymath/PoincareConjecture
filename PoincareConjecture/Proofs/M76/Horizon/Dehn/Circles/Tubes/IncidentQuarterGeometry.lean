import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.JointDiamondMap

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.SignedJointCross

local notation "P2" => (ℝ × ℝ)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (J : SignedJointCross E)

theorem incident_quarter_geometry
    (mu : Fin 2 → E → ℝ) (swap : Bool) (eta signs : Fin 2 → Bool)
    (hzero : ∀ j z, z ∈ J.disk →
      (J.coordinate j z = 0 ↔ mu (jointSheetIndex swap j) z = 0))
    (hside : ∀ j b z, z ∈ J.disk →
      (side b (J.coordinate j z) ↔
        side (if eta j then b else !b) (mu (jointSheetIndex swap j) z))) :
    let Q := {z | z ∈ J.disk ∧ ∀ j, side (signs j) (mu j z)}
    let U := (Q ∩ {z | mu 0 z = 0}) ∪ (Q ∩ {z | mu 1 z = 0})
    let O := Q ∩ J.rim
    ∃ a b : E, a ≠ b ∧ IsFinitePLBallPair P2 Q (O ∪ U) ∧
      IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ O {a, b} ∧ U ∩ O = {a, b} := by
  let Q := {z | z ∈ J.disk ∧ ∀ j, side (signs j) (mu j z)}
  let U := (Q ∩ {z | mu 0 z = 0}) ∪ (Q ∩ {z | mu 1 z = 0})
  let O := Q ∩ J.rim
  let ss (j : Fin 2) := if eta j then signs (jointSheetIndex swap j) else
    !(signs (jointSheetIndex swap j))
  have hidx (j : Fin 2) : jointSheetIndex swap (jointSheetIndex swap j) = j := by
    cases swap <;> simp [jointSheetIndex]
  have hsign (j : Fin 2) (z : E) (hz : z ∈ J.disk) :
      side (ss j) (J.coordinate j z) ↔ side (signs (jointSheetIndex swap j))
        (mu (jointSheetIndex swap j) z) := by
    have h := hside j (ss j) z hz
    cases he : eta j <;> simpa only [ss, he, Bool.false_eq_true, if_false, if_true,
      Bool.not_not] using h
  have hQ : Q = J.quarter (ss 0) (ss 1) := by
    ext z
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, (hsign 0 z hz).mpr (h _), (hsign 1 z hz).mpr (h _)⟩
    · rintro ⟨hz, h0, h1⟩
      refine ⟨hz, ?_⟩
      intro k
      have hj : ∀ j, side (ss j) (J.coordinate j z) := by
        intro j
        fin_cases j
        · exact h0
        · exact h1
      simpa only [hidx] using (hsign (jointSheetIndex swap k) z hz).mp (hj _)
  have hzeros (z : E) (hz : z ∈ J.disk) :
      (mu 0 z = 0 ∨ mu 1 z = 0) ↔ (J.coordinate 0 z = 0 ∨ J.coordinate 1 z = 0) := by
    have h0 := hzero 0 z hz
    have h1 := hzero 1 z hz
    cases swap
    · exact (or_congr h0 h1).symm
    · exact or_comm.trans (or_congr h0 h1).symm
  have hU : U = J.radius 0 (ss 1) ∪ J.radius 1 (ss 0) := by
    rw [← J.quarter_axis_zero (ss 0) (ss 1), ← J.quarter_axis_one (ss 0) (ss 1)]
    ext z
    change ((z ∈ Q ∧ mu 0 z = 0) ∨ (z ∈ Q ∧ mu 1 z = 0)) ↔ _
    constructor
    · intro hz
      have hzQ : z ∈ Q := hz.elim And.left And.left
      have hz0 := (hzeros z hzQ.1).mp (hz.elim (Or.inl ∘ And.right) (Or.inr ∘ And.right))
      exact hz0.elim (fun h => Or.inl ⟨hQ.subset hzQ, hzQ.1, h⟩)
        (fun h => Or.inr ⟨hQ.subset hzQ, hzQ.1, h⟩)
    · intro hz
      have hzQ : z ∈ Q := hQ.symm.subset (hz.elim And.left And.left)
      have hz0 := (hzeros z hzQ.1).mpr
        (hz.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2))
      exact hz0.elim (fun h => Or.inl ⟨hzQ, h⟩) (fun h => Or.inr ⟨hzQ, h⟩)
  have hO : O = J.quarter (ss 0) (ss 1) ∩ J.rim := congrArg (fun A => A ∩ J.rim) hQ
  have hab : J.endpoint 0 (ss 1) ≠ J.endpoint 1 (ss 0) := by
    intro he
    exact J.endpoint_ne_center 0 (ss 1) ((J.cross_radii (ss 0) (ss 1)).subset
      ⟨right_mem_segment ℝ _ _, he ▸ right_mem_segment ℝ _ _⟩)
  have hg := J.quarter_boundary_arcs (ss 0) (ss 1)
  change ∃ a b : E, a ≠ b ∧ IsFinitePLBallPair P2 Q (O ∪ U) ∧
    IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ O {a, b} ∧ U ∩ O = {a, b}
  refine ⟨J.endpoint 0 (ss 1), J.endpoint 1 (ss 0), hab, ?_, ?_, ?_, ?_⟩
  · simpa only [hQ, hU, hO] using J.quarter_ball (ss 0) (ss 1)
  · simpa only [hU] using hg.1
  · simpa only [hO] using hg.2.1
  · simpa only [hU, hO] using hg.2.2

end PoincareConjecture.M76.Dehn.SignedJointCross
