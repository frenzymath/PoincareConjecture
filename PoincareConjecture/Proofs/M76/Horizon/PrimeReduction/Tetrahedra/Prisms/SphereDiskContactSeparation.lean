import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem sphere_boundary_disk_contact_subset_rim
    {B R N n C c : Set E} (hB : IsFinitePLBallPair V B R)
    (hdim : Module.finrank ℝ V = 3)
    (hN : IsFinitePLBallPair (ℝ × ℝ) N n) (hC : IsFinitePLBallPair (ℝ × ℝ) C c)
    (hNR : N ⊆ R) (hCR : C ⊆ R) (hcontact : N ∩ C ⊆ c) : N ∩ C ⊆ n := by
  obtain ⟨p,hpC,hpc⟩ := hC.sdiff_nonempty
  have hpN : p ∉ N := fun hp => hpc (hcontact ⟨hp,hpC⟩)
  have hcomp := hB.boundary_disk_complement hdim hN hNR ⟨p,hCR hpC,hpN⟩
  have hcore : C \ c ⊆ R \ (N \ n) := by
    intro x hx
    refine ⟨hCR hx.1,?_⟩
    intro hxN
    exact hx.2 (hcontact ⟨hxN.1,hx.1⟩)
  have hsub : C ⊆ R \ (N \ n) := by
    rw [←hC.closure_sdiff]
    exact closure_minimal hcore hcomp.isCompact.isClosed
  intro x hx
  by_contra hxn
  exact (hsub hx.2).2 ⟨hx.1,hxn⟩

theorem not_three_boundary_disk_pages
    {B R A a C c D d W : Set E} {p q : E}
    (hB : IsFinitePLBallPair V B R) (hdim : Module.finrank ℝ V = 3)
    (hA : IsFinitePLBallPair (ℝ × ℝ) A a)
    (hC : IsFinitePLBallPair (ℝ × ℝ) C c)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D d)
    (hW : IsFinitePLBallPair ℝ W {p,q}) (hpq : p ≠ q)
    (hWa : W ⊆ a) (hWc : W ⊆ c) (hAC : A ∩ C = W)
    (hAR : A ⊆ R) (hCR : C ⊆ R) (hDR : D ⊆ R)
    (hcontact : (A ∪ C) ∩ D ⊆ d) (hWD : W ⊆ D) : False := by
  have hUnion := hA.union_of_boundary_interval hC hW hWa hWc hpq hAC
  have hboundary := sphere_boundary_disk_contact_subset_rim hB hdim hUnion hD
    (union_subset hAR hCR) hDR hcontact
  obtain ⟨x,hxW,hxends⟩ := hW.sdiff_nonempty
  have hxA := hA.1 (hWa hxW)
  have hxN := hboundary ⟨Or.inl hxA,hWD hxW⟩
  exact hxN.2 ⟨hxW,hxends⟩

end PoincareConjecture.M76.PrismBelt
