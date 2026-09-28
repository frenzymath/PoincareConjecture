import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnulusSphereComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AttachmentAnnulusProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.AnnularBallProduct

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_protected_ball_product_of_annulus_with_height
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S A : Set E} (hB : IsFinitePLBallPair V3 B S)
    (H : Ann ≃ₜ A) (hH : H.IsFinitePL) (hAS : A ⊆ S) :
    ∃ (d r : Bool → Set E) (P : B ≃ₜ (d false ×ˢ I : Set (E × ℝ))),
      (∀ i, IsFinitePLBallPair P2 (d i) (r i) ∧ d i ⊆ S ∧
        d i ∩ A = r i ∧ r i = (fun z : Ann => (H z : E)) ''
          {z | depth 8 z = if i then 1 else -1}) ∧
      Disjoint (d true) (d false) ∧ (d true ∪ d false) ∪ A = S ∧
      P.IsFinitePL ∧
      (∀ i (x : B), (x : E) ∈ d i ↔
        (P x : E × ℝ) ∈ d false ×ˢ {if i then (1 : ℝ) else 0}) ∧
      (∀ x : B, (x : E) ∈ A ↔ (P x : E × ℝ) ∈ r false ×ˢ I) ∧
      ∀ z : Ann, (P ⟨H z, hB.1 (hAS (H z).property)⟩ : E × ℝ).2 =
        (depth 8 (z : P2) + 1) / 2 := by
  obtain ⟨d,r,hd,hdis,hcover⟩ := exists_annulus_sphere_complement_disks hB H hH hAS
  obtain ⟨e,he,hemem,heheight⟩ :=
    exists_attachment_annulus_product_with_height H hH r (fun i => (hd i).2.2.2)
  have hbound : S = A ∪ (d false ∪ d true) := by
    rw [← hcover]
    ac_rfl
  have hB' : IsFinitePLBallPair V3 B (A ∪ (d false ∪ d true)) := hbound ▸ hB
  obtain ⟨P,hP,hkeep,hPc,hPa⟩ := hB'.exists_product_extending_annulus d r
    (fun i => (hd i).1) (fun i => (hd i).2.2.1) hdis e he hemem
  refine ⟨d,r,P,hd,hdis,hcover,hP,hPc,hPa,?_⟩
  intro z
  have hvalue := congrArg Prod.snd (hkeep (H z))
  change (P ⟨H z, hB.1 (hAS (H z).property)⟩ : E × ℝ).2 = (e (H z) : E × ℝ).2 at hvalue
  rw [hvalue, heheight, H.symm_apply_apply]

theorem exists_protected_ball_product_of_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S A : Set E} (hB : IsFinitePLBallPair V3 B S)
    (H : Ann ≃ₜ A) (hH : H.IsFinitePL) (hAS : A ⊆ S) :
    ∃ (d r : Bool → Set E) (P : B ≃ₜ (d false ×ˢ I : Set (E × ℝ))),
      (∀ i, IsFinitePLBallPair P2 (d i) (r i) ∧ d i ⊆ S ∧
        d i ∩ A = r i ∧ r i = (fun z : Ann => (H z : E)) ''
          {z | depth 8 z = if i then 1 else -1}) ∧
      Disjoint (d true) (d false) ∧ (d true ∪ d false) ∪ A = S ∧
      P.IsFinitePL ∧
      (∀ i (x : B), (x : E) ∈ d i ↔
        (P x : E × ℝ) ∈ d false ×ˢ {if i then (1 : ℝ) else 0}) ∧
      ∀ x : B, (x : E) ∈ A ↔ (P x : E × ℝ) ∈ r false ×ˢ I := by
  obtain ⟨d, r, P, hd, hdis, hcover, hP, hPc, hPa, _⟩ :=
    exists_protected_ball_product_of_annulus_with_height hB H hH hAS
  exact ⟨d, r, P, hd, hdis, hcover, hP, hPc, hPa⟩

end PoincareConjecture.M76
