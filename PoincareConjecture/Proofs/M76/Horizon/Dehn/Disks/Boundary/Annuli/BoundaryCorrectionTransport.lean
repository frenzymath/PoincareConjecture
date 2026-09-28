import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.ProperDiskCorrection

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A2" => squareAnnulus 8 1


def annulusChartImage {X : Type*} [TopologicalSpace X] {T : Set X} {L d : ℝ}
    (c : squareAnnulus L d ≃ₜ T) (S : Set P2) : Set X :=
  (fun p : squareAnnulus L d ↦ (c p : X)) ''
    ((Subtype.val : squareAnnulus L d → P2) ⁻¹' S)

theorem annulusChartImage_subset {X : Type*} [TopologicalSpace X]
    {T : Set X} {L d : ℝ} (c : squareAnnulus L d ≃ₜ T) (S : Set P2) :
    annulusChartImage c S ⊆ T := by
  rintro z ⟨p, _, rfl⟩
  exact (c p).property



theorem exists_transported_boundary_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T : Set E} {L d : ℝ} (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL)
    {A : Set P2} (hA : A ⊆ squareAnnulus L d) (a : A2 ≃ₜ A) (ha : a.IsFinitePL) :
    ∃ b : A2 ≃ₜ annulusChartImage c A, b.IsFinitePL ∧ b.symm.IsFinitePL ∧
      (∀ p : A2, (b p : E) = c ⟨a p, hA (a p).property⟩) ∧
      ∀ u : ℝ, annulusDepthImage b u = annulusChartImage c (annulusDepthImage a u) := by
  obtain ⟨f, hf, hfv⟩ := hc
  obtain ⟨g, hg, hgv⟩ := ha
  have hgmap : MapsTo g A2 (squareAnnulus L d) := by
    intro p hp
    rw [← hgv ⟨p, hp⟩]
    exact hA (a ⟨p, hp⟩).property
  have hfi : InjOn f (squareAnnulus L d) := by
    intro x hx y hy hxy
    have hh : c ⟨x, hx⟩ = c ⟨y, hy⟩ :=
      Subtype.ext ((hfv ⟨x, hx⟩).trans (hxy.trans (hfv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (c.injective hh)
  have hgi : InjOn g A2 := by
    intro x hx y hy hxy
    have hh : a ⟨x, hx⟩ = a ⟨y, hy⟩ :=
      Subtype.ext ((hgv ⟨x, hx⟩).trans (hxy.trans (hgv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (a.injective hh)
  have hk := hf.comp hg hgmap
  obtain ⟨b₀, hb₀, hb₀val⟩ := hk.exists_homeomorph_image (hfi.comp hgi hgmap)
  have himage : (f ∘ g) '' A2 = annulusChartImage c A := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨g p, hgmap hp⟩, ?_, ?_⟩
      · change g p ∈ A
        rw [← hgv ⟨p, hp⟩]
        exact (a ⟨p, hp⟩).property
      · exact hfv ⟨g p, hgmap hp⟩
    · rintro ⟨p, hp, rfl⟩
      let q := a.symm ⟨p, hp⟩
      refine ⟨q, q.property, ?_⟩
      change f (g q) = (c p : E)
      rw [← hgv q]
      have hh : (a q : P2) = p := congrArg Subtype.val (a.apply_symm_apply ⟨p, hp⟩)
      rw [hh]
      exact (hfv p).symm
  let b := b₀.trans (Homeomorph.setCongr himage)
  have hb : b.IsFinitePL := ⟨f ∘ g, hk, fun p ↦ hb₀val p⟩
  have hval (p : A2) : (b p : E) = c ⟨a p, hA (a p).property⟩ := by
    change (b₀ p : E) = _
    rw [hb₀val]
    change f (g p) = _
    rw [← hgv p]
    exact (hfv ⟨a p, hA (a p).property⟩).symm
  refine ⟨b, hb, hb.symm, hval, ?_⟩
  intro u
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨a p, hA (a p).property⟩, ⟨p, hp, rfl⟩, (hval p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqp⟩ := hp
    refine ⟨q, hq, ?_⟩
    exact (hval q).trans
      (congrArg (fun w : squareAnnulus L d ↦ (c w : E)) (Subtype.ext hqp))




theorem exists_proper_disk_boundary_correction_through_annulus
    {R B T : Set V3} {L d : ℝ} (hR : IsCompact R)
    (he : PLDomain (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL) (hT : T ⊆ frontier R)
    {A₀ A₁ S₀ S₁ Q : Set P2}
    (hA₀ : A₀ ⊆ squareAnnulus L d) (hA₁ : A₁ ⊆ squareAnnulus L d)
    (a₀ : A2 ≃ₜ A₀) (a₁ : A2 ≃ₜ A₁)
    (ha₀ : a₀.IsFinitePL) (ha₁ : a₁.IsFinitePL)
    (h₀inner : annulusDepthImage a₀ 1 = S₀)
    (h₁inner : annulusDepthImage a₁ 1 = S₁)
    (h₀outer : annulusDepthImage a₀ (-1) = Q)
    (h₁outer : annulusDepthImage a₁ (-1) = Q)
    (hB : IsFinitePLBallPair P2 B (annulusChartImage c S₀)) (hBR : B ⊆ R) :
    ∃ Bnew : Set V3, IsFinitePLBallPair P2 Bnew (annulusChartImage c S₁) ∧
      Bnew ⊆ R ∧ Bnew ∩ frontier R = annulusChartImage c S₁ := by
  obtain ⟨b₀, hb₀, _, _, hb₀depth⟩ := exists_transported_boundary_annulus c hc hA₀ a₀ ha₀
  obtain ⟨b₁, hb₁, _, _, hb₁depth⟩ := exists_transported_boundary_annulus c hc hA₁ a₁ ha₁
  exact exists_proper_disk_boundary_correction hR he hB hBR b₀ b₁ hb₀ hb₁
    ((annulusChartImage_subset c A₀).trans hT)
    ((annulusChartImage_subset c A₁).trans hT)
    ((hb₀depth 1).trans (congrArg (annulusChartImage c) h₀inner))
    ((hb₁depth 1).trans (congrArg (annulusChartImage c) h₁inner))
    ((hb₀depth (-1)).trans (congrArg (annulusChartImage c) h₀outer))
    ((hb₁depth (-1)).trans (congrArg (annulusChartImage c) h₁outer))

end PoincareConjecture.M76.Dehn
