import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Preservation



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_first_source_point_of_marked_intersection
    {E X : Type*} {S Q : Set E} {F : Set X} {f g : E → X}
    (hgi : InjOn g S) (hgmark : ∀ x ∈ S, g x ∈ F ↔ x ∈ Q)
    (p : X) (hpoint : ((f '' S) ∩ (g '' S)) ∩ F = {p}) :
    ∃ a : E, (S ∩ g ⁻¹' (f '' S)) ∩ Q = {a} := by
  have hp := hpoint.superset (mem_singleton p)
  obtain ⟨a, ha, hap⟩ := hp.1.2
  have haQ : a ∈ Q := (hgmark a ha).mp (hap.symm ▸ hp.2)
  refine ⟨a, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨⟨hx, hxf⟩, hxQ⟩
    have hxp : g x = p := hpoint.subset ⟨⟨hxf, ⟨x, hx, rfl⟩⟩, (hgmark x hx).mpr hxQ⟩
    exact hgi hx ha (hxp.trans hap.symm)
  · intro x hx
    have hxa : x = a := hx
    subst x
    exact ⟨⟨ha, show g a ∈ f '' S from hap.symm ▸ hp.1.1⟩, haQ⟩

theorem protected_mark_iff_of_boundary_replacement
    {E X : Type*} [TopologicalSpace X] {S Q H : Set E} {R F₀ F₁ : Set X}
    {f k : E → X} (hF₀ : F₀ ⊆ frontier R) (hdis : Disjoint F₀ F₁)
    (hproper : ∀ x ∈ S, k x ∈ frontier R ↔ x ∈ Q ∪ H)
    (hkeep : EqOn k f (S ∩ H)) (houter : MapsTo k (S ∩ Q) F₁)
    (hmark : ∀ x ∈ S, f x ∈ F₀ ↔ x ∈ H) :
    ∀ x ∈ S, k x ∈ F₀ ↔ x ∈ H := by
  intro x hx
  constructor
  · intro hk
    rcases (hproper x hx).mp (hF₀ hk) with hq | hh
    · exact (disjoint_left.mp hdis hk (houter ⟨hx, hq⟩)).elim
    · exact hh
  · intro hh
    rw [hkeep ⟨hx, hh⟩]
    exact (hmark x hx).mpr hh

theorem protected_marked_intersection_of_boundary_replacement
    {E X : Type*} {S H : Set E} {F : Set X} {f g k : E → X}
    (hkeep : EqOn k f (S ∩ H))
    (hf : ∀ x ∈ S, f x ∈ F ↔ x ∈ H)
    (hk : ∀ x ∈ S, k x ∈ F ↔ x ∈ H) :
    ((k '' S) ∩ (g '' S)) ∩ F = ((f '' S) ∩ (g '' S)) ∩ F := by
  ext y
  constructor
  · rintro ⟨⟨⟨x, hx, rfl⟩, hyG⟩, hyF⟩
    have hv := hkeep ⟨hx, (hk x hx).mp hyF⟩
    exact ⟨⟨⟨x, hx, hv.symm⟩, hyG⟩, hyF⟩
  · rintro ⟨⟨⟨x, hx, rfl⟩, hyG⟩, hyF⟩
    exact ⟨⟨⟨x, hx, hkeep ⟨hx, (hf x hx).mp hyF⟩⟩, hyG⟩, hyF⟩

end PoincareConjecture.M76.Dehn.Annuli
