import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripExteriorDisks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.HoleSelection

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_nonspanning_strip_exterior_annulus
    {S T : Set P2} (hT : IsFinitePLBallPair P2 T (frontier T)) (c : Bool → P2 → P2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source T)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ (frontier T) ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hS : IsFinitePLBallPair P2 S (frontier S)) (hST : S ⊆ interior T)
    (havoid : Disjoint ((c false '' source) ∪ (c true '' source)) S) :
    ∃ (A M C : Set P2) (s0 s1 : Bool),
      IsFinitePLBallPair P2 A ((A ∩ (frontier T)) ∪ c false '' arm (farArmParameter (!s0))) ∧
      IsFinitePLBallPair P2 M
        (((M ∩ (frontier T)) ∪ c false '' arm (farArmParameter s0)) ∪
          c true '' arm (farArmParameter s1)) ∧
      IsFinitePLBallPair P2 C ((C ∩ (frontier T)) ∪ c true '' arm (farArmParameter (!s1))) ∧
      Disjoint A M ∧ Disjoint M C ∧ Disjoint A C ∧
      ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = T ∧
      (c false '' source) ∩ A = c false '' arm (farArmParameter (!s0)) ∧
      (c false '' source) ∩ M = c false '' arm (farArmParameter s0) ∧
      (c true '' source) ∩ M = c true '' arm (farArmParameter s1) ∧
      (c true '' source) ∩ C = c true '' arm (farArmParameter (!s1)) ∧
      Disjoint A (c true '' source) ∧ Disjoint C (c false '' source) ∧
      ∃ D : Set P2, (D = A ∨ D = M ∨ D = C) ∧ S ⊆ interior D ∧
        (∀ E ∈ ({A, M, C} : Set (Set P2)), E ≠ D → Disjoint E S) ∧
        ∃ H : squareAnnulus 8 1 ≃ₜ (D \ interior S : Set P2), H.IsFinitePL ∧
          (∀ z : squareAnnulus 8 1,
            depth 8 (z : P2) = -1 ↔ (H z : P2) ∈ frontier D) ∧
          ∀ z : squareAnnulus 8 1,
            depth 8 (z : P2) = 1 ↔ (H z : P2) ∈ frontier S := by
  obtain ⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0⟩ :=
    exists_strip_exterior_disks hT c hcPL hci hcS hcQ hdisj
  let X := (c false '' source) ∪ (c true '' source)
  have hfar (i s : Bool) : c i '' arm (farArmParameter s) ⊆ X := by
    intro x hx
    have h := image_mono (arm_far_subset_source s) hx
    cases i with
    | false => exact Or.inl h
    | true => exact Or.inr h
  have hQA : (A ∩ frontier T) ∪ c false '' arm (farArmParameter (!s0)) ⊆
      frontier T ∪ X := by
    rintro x (hx | hx)
    · exact Or.inl hx.2
    · exact Or.inr (hfar false (!s0) hx)
  have hQM : ((M ∩ frontier T) ∪ c false '' arm (farArmParameter s0)) ∪
      c true '' arm (farArmParameter s1) ⊆ frontier T ∪ X := by
    rintro x ((hx | hx) | hx)
    · exact Or.inl hx.2
    · exact Or.inr (hfar false s0 hx)
    · exact Or.inr (hfar true s1 hx)
  have hQC : (C ∩ frontier T) ∪ c true '' arm (farArmParameter (!s1)) ⊆
      frontier T ∪ X := by
    rintro x (hx | hx)
    · exact Or.inl hx.2
    · exact Or.inr (hfar true (!s1) hx)
  exact ⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0,
    exists_annular_member_of_disjoint_disk_exteriors hS hST hA hM hC
      hAM hMC hAC hcover havoid hQA hQM hQC⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
