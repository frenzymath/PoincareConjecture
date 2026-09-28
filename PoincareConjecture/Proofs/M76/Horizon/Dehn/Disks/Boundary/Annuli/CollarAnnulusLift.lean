import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.AnnulusHeightGraphs

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "A2" => squareAnnulus 8 1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def annulusDepthImage {A : Set E} (a : A2 ≃ₜ A) (u : ℝ) : Set E :=
  (fun p : A2 ↦ (a p : E)) '' {p | depth 8 (p : P2) = u}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem annulusDepthImage_subset {A : Set E} (a : A2 ≃ₜ A) (u : ℝ) :
    annulusDepthImage a u ⊆ A := by
  rintro z ⟨p, _, rfl⟩
  exact (a p).property

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem mem_annulusDepthImage_iff {A : Set E} (a : A2 ≃ₜ A) (u : ℝ) (p : A2) :
    (a p : E) ∈ annulusDepthImage a u ↔ depth 8 (p : P2) = u := by
  constructor
  · rintro ⟨q, hq, heq⟩
    exact a.injective (Subtype.ext heq) ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem exists_boundary_annulus_lift {L : SimplicialComplex ℝ E} {R A : Set F}
    (HB : L.space ≃ₜ frontier R) (hHB : HB.IsFinitePL)
    (a : A2 ≃ₜ A) (ha : a.IsFinitePL) (hA : A ⊆ frontier R) :
    ∃ (S : Set E) (b : A2 ≃ₜ S), S ⊆ L.space ∧ b.IsFinitePL ∧
      ∀ p : A2, (b p : E) = HB.symm ⟨a p, hA (a p).property⟩ := by
  obtain ⟨g, hg, hgv⟩ := hHB.symm
  obtain ⟨f, hf, hfv⟩ := ha
  have hfmap : MapsTo f A2 (frontier R) := by
    intro p hp
    rw [← hfv ⟨p, hp⟩]
    exact hA (a ⟨p, hp⟩).property
  have hk := hg.comp hf hfmap
  have hgi : InjOn g (frontier R) := by
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

end PoincareConjecture.M76.Dehn
