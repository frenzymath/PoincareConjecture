import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.PhaseContactTransfer
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.JointPLComposition



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_projected_two_moves (c : ℝ) {D E : Set P2} {a b : ℝ}
    (hD : IsFinitePLBallPair P2 D (frontier D))
    (hE : IsFinitePLBallPair P2 E (frontier E))
    (hwidth : b - a < 32) (ha : a ≤ 0) (hb : 0 ≤ b)
    (hstrip : D ∪ E ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc a b)
    (H J : I → P2 ≃ₜ P2)
    (hzero : H 0 = Homeomorph.refl P2) (jzero : J 0 = Homeomorph.refl P2)
    (hfix : ∀ t x, x ∉ interior D → H t x = x)
    (jfix : ∀ t x, x ∉ interior E → J t x = x)
    (hc : Continuous (fun z : I × P2 => H z.1 z.2))
    (hci : Continuous (fun z : I × P2 => (H z.1).symm z.2))
    (jc : Continuous (fun z : I × P2 => J z.1 z.2))
    (jci : Continuous (fun z : I × P2 => (J z.1).symm z.2))
    (f fi g gi : (ℝ × P2) → P2)
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1 ×ˢ D))
    (hfi : FinitePiecewiseAffineOn fi (Icc (0 : ℝ) 1 ×ˢ D))
    (hg : FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ E))
    (hgi : FinitePiecewiseAffineOn gi (Icc (0 : ℝ) 1 ×ˢ E))
    (hv : ∀ t : I, ∀ x : D, f (t, x) = H t x)
    (hiv : ∀ t : I, ∀ x : D, fi (t, x) = (H t).symm x)
    (jv : ∀ t : I, ∀ x : E, g (t, x) = J t x)
    (jiv : ∀ t : I, ∀ x : E, gi (t, x) = (J t).symm x) :
    ∃ G : Ann ≃ₜ Ann, HasJointPLAnnularIsotopy G ∧
      (∀ (x : Ann) (y : P2), y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
        (x : P2) = annularLiftProjectionAt c y →
        (G x : P2) = annularLiftProjectionAt c (J 1 (H 1 y))) ∧
      ∀ (x : Ann) (r : P2), r.2 ∈ Icc (-1 : ℝ) 1 →
        (x : P2) = annulusMap 8 (by norm_num) ((r.1 : Circle), r.2) →
        (G x ∈ range (fun t : I => annulusCylinderHomeomorph (t, (c : Circle))) ↔
          ∃ k : ℤ, (J 1 (H 1 (r.2, r.1 - (c + 32 * (k : ℝ))))).2 = 0) := by
  have hDS := fun x hx => hstrip (Or.inl hx : x ∈ D ∪ E)
  have hES := fun x hx => hstrip (Or.inr hx : x ∈ D ∪ E)
  have hDT : D ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
    fun x hx => ⟨Ioo_subset_Icc_self (hDS x hx).1, (hDS x hx).2⟩
  have hET : E ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
    fun x hx => ⟨Ioo_subset_Icc_self (hES x hx).1, (hES x hx).2⟩
  obtain ⟨A, F, Fi, hA0, hF, hFi, hFv, hFiv, hAc, hAci, hAr, hAo, hAa, _⟩ :=
    exists_projected_annular_disk_motion_at_phase c hD hwidth hDS H hzero hfix hc hci
      f fi hf hfi hv hiv
  obtain ⟨B, Q, Qi, hB0, hQ, hQi, hQv, hQiv, hBc, hBci, hBr, hBo, hBa, _⟩ :=
    exists_projected_annular_disk_motion_at_phase c hE hwidth hES J jzero jfix jc jci
      g gi hg hgi jv jiv
  have hA : HasJointPLAnnularIsotopy (A 1) :=
    ⟨A, F, Fi, hA0, rfl, hF, hFi, hFv, hFiv, hAc, hAci, hAr⟩
  have hB : HasJointPLAnnularIsotopy (B 1) :=
    ⟨B, Q, Qi, hB0, rfl, hQ, hQi, hQv, hQiv, hBc, hBci, hBr⟩
  refine ⟨(A 1).trans (B 1), hA.trans hB, ?_, ?_⟩
  · exact projected_two_moves_eq_on_window hwidth hDT hET (H 1) (J 1)
      (hfix 1) (jfix 1) (A 1) (B 1) (hAo 1) (hBo 1) (hAa 1) (hBa 1)
  · exact projected_two_moves_radial_contact_iff hwidth ha hb hDT hET (H 1) (J 1)
      (hfix 1) (jfix 1) (A 1) (B 1) (hAo 1) (hBo 1) (hAa 1) (hBa 1)

end PoincareConjecture.M76.Dehn
