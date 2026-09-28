import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.BoundaryAgreement

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

theorem proper_rim_fixed_mark_iff
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {S : Set E} {R F : Set X} {f k : E → X}
    (hF : F ⊆ frontier R)
    (hfproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ frontier S)
    (hkproper : ∀ x ∈ S, k x ∈ frontier R ↔ x ∈ frontier S)
    (hkeep : EqOn k f (frontier S)) :
    ∀ x ∈ S, k x ∈ F ↔ f x ∈ F := by
  intro x hx
  constructor
  · intro hh
    rwa [hkeep ((hkproper x hx).mp (hF hh))] at hh
  · intro hh
    rwa [hkeep ((hfproper x hx).mp (hF hh))]

theorem proper_rim_fixed_marked_intersection
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {S : Set E} {R F A : Set X} {f k : E → X}
    (hF : F ⊆ frontier R)
    (hfproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ frontier S)
    (hkproper : ∀ x ∈ S, k x ∈ frontier R ↔ x ∈ frontier S)
    (hkeep : EqOn k f (frontier S)) :
    ((k '' S) ∩ A) ∩ F = ((f '' S) ∩ A) ∩ F := by
  ext y
  constructor
  · rintro ⟨⟨⟨x,hx,rfl⟩,hyA⟩,hyF⟩
    have hv := hkeep ((hkproper x hx).mp (hF hyF))
    exact ⟨⟨⟨x,hx,hv.symm⟩,hyA⟩,hyF⟩
  · rintro ⟨⟨⟨x,hx,rfl⟩,hyA⟩,hyF⟩
    have hv := hkeep ((hfproper x hx).mp (hF hyF))
    exact ⟨⟨⟨x,hx,hv⟩,hyA⟩,hyF⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
