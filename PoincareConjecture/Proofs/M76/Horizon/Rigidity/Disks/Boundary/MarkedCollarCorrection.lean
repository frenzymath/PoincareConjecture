import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteInwardCompression
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.CollarAnnulusLift
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.DiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology
open PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "A2" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_marked_annulus_lift {L : SimplicialComplex ℝ E} {B A : Set F}
    (HB : L.space ≃ₜ B) (hHB : HB.IsFinitePL)
    (a : A2 ≃ₜ A) (ha : a.IsFinitePL) (hA : A ⊆ B) :
    ∃ (S : Set E) (b : A2 ≃ₜ S), S ⊆ L.space ∧ b.IsFinitePL ∧
      ∀ p : A2, (b p : E) = HB.symm ⟨a p, hA (a p).property⟩ := by
  obtain ⟨g, hg, hgv⟩ := hHB.symm
  obtain ⟨f, hf, hfv⟩ := ha
  have hfmap : MapsTo f A2 (B) := by
    intro p hp
    rw [← hfv ⟨p, hp⟩]
    exact hA (a ⟨p, hp⟩).property
  have hk := hg.comp hf hfmap
  have hgi : InjOn g (B) := by
    intro x hx y hy heq
    have hh : HB.symm ⟨x, hx⟩ = HB.symm ⟨y, hy⟩ :=
      Subtype.ext ((hgv ⟨x, hx⟩).trans (heq.trans (hgv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (HB.symm.injective hh)
  have hfi : InjOn f A2 := by
    intro x hx y hy heq
    have hh : a ⟨x, hx⟩ = a ⟨y, hy⟩ :=
      Subtype.ext ((hfv ⟨x, hx⟩).trans (heq.trans (hfv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (a.injective hh)
  obtain ⟨b, hb, hbval⟩ := hk.exists_homeomorph_image (hgi.comp hfi hfmap)
  have hval (p : A2) : (b p : E) = HB.symm ⟨a p, hA (a p).property⟩ := by
    rw [hbval]
    change g (f p) = _
    rw [← hfv p]
    exact (hgv ⟨a p, hA (a p).property⟩).symm
  refine ⟨_, b, ?_, hb, hval⟩
  intro z hz
  obtain ⟨p, hp⟩ := b.surjective ⟨z, hz⟩
  have heq : (b p : E) = z := congrArg Subtype.val hp
  rw [← heq, hval]
  exact (HB.symm ⟨a p, hA (a p).property⟩).property

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
theorem correction_annulus_graph_mark
    {L : SimplicialComplex ℝ E} {c : E × ℝ → F} {B : Set F}
    (hfront : ∀ z ∈ L.space ×ˢ I, c z ∈ B ↔ z.2 = 0)
    (a : A2 → E) (ha : ∀ p, a p ∈ L.space) (p : A2) :
    c (a p, annulusCorrectionHeight true p) ∉ B ∧
      (c (a p, annulusCorrectionHeight false p) ∈ B ↔ depth 8 p = 1) := by
  have hp := mem_squareAnnulus_iff_depth.mp p.property
  have hu := hfront (a p, annulusCorrectionHeight true p)
    ⟨ha p, (annulusCorrectionHeight_bounds true p).1⟩
  have hl := hfront (a p, annulusCorrectionHeight false p)
    ⟨ha p, (annulusCorrectionHeight_bounds false p).1⟩
  constructor
  · intro h
    have hh := hu.mp h
    change (3 + depth 8 p) / 8 = 0 at hh
    linarith [hp.1]
  · exact hl.trans ⟨fun h ↦ by change (1 - depth 8 p) / 8 = 0 at h; linarith,
      fun h ↦ by change (1 - depth 8 p) / 8 = 0; linarith⟩

end PoincareConjecture.M76
