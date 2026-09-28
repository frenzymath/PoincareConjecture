import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.PairedDisks



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q₀" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Q₁" => Set.ofPred (fun x : P2 => depth 8 x = 1)
local notation "Rim" => Q₀ ∪ Q₁

theorem annulus_first_mark_iff_of_proper
    {X : Type*} [TopologicalSpace X] {R : Set X} {F : Bool → Set X} {f : P2 → X}
    (hF : ∀ b, F b ⊆ frontier R) (hdis : Disjoint (F false) (F true))
    (hproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ Rim)
    (hmark : ∀ x ∈ Ann, ∀ b, depth 8 x = (if b then 1 else -1) → f x ∈ F b) :
    ∀ x ∈ Ann, f x ∈ F false ↔ x ∈ Q₀ := by
  intro x hx
  constructor
  · intro hxf
    rcases (hproper x hx).mp (hF false hxf) with h | h
    · exact h
    · exact (disjoint_left.mp hdis hxf (hmark x hx true h)).elim
  · exact hmark x hx false

theorem exists_both_source_first_marked_points
    {X : Type*} {F : Set X} {f g : P2 → X}
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F ↔ x ∈ Q₀)
    (hgmark : ∀ x ∈ Ann, g x ∈ F ↔ x ∈ Q₀)
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F = {p}) :
    ∃ a b : P2, a ∈ Q₀ ∧ b ∈ Q₀ ∧ f a = p ∧ g b = p ∧
      (Ann ∩ f ⁻¹' (g '' Ann)) ∩ Q₀ = {a} ∧
      (Ann ∩ g ⁻¹' (f '' Ann)) ∩ Q₀ = {b} := by
  have hp := hpoint.symm.subset (mem_singleton p)
  obtain ⟨a,ha,hap⟩ := hp.1.1
  obtain ⟨b,hb,hbp⟩ := hp.1.2
  have haQ := (hfmark a ha).mp (hap.symm ▸ hp.2)
  have hbQ := (hgmark b hb).mp (hbp.symm ▸ hp.2)
  refine ⟨a,b,haQ,hbQ,hap,hbp,?_,?_⟩
  · apply Subset.antisymm
    · intro x hx
      have hxp : f x = p := hpoint.subset
        ⟨⟨⟨x,hx.1.1,rfl⟩,hx.1.2⟩,(hfmark x hx.1.1).mpr hx.2⟩
      exact hfi hx.1.1 ha (hxp.trans hap.symm)
    · rintro x rfl
      exact ⟨⟨ha,⟨b,hb,hbp.trans hap.symm⟩⟩,haQ⟩
  · apply Subset.antisymm
    · intro x hx
      have hxp : g x = p := hpoint.subset
        ⟨⟨hx.1.2,⟨x,hx.1.1,rfl⟩⟩,(hgmark x hx.1.1).mpr hx.2⟩
      exact hgi hx.1.1 hb (hxp.trans hbp.symm)
    · rintro x rfl
      exact ⟨⟨hb,⟨a,ha,hap.trans hbp.symm⟩⟩,hbQ⟩

end PoincareConjecture.M76.Dehn.Annuli
