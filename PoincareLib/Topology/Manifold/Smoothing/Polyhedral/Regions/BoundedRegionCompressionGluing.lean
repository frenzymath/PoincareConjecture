import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLTransport
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.CompactHomeomorphGluing

/-!
# Gluing a finite PL compression to the identity

The closed remainder need not have a separately supplied
triangulation. Compact pasting gives a homeomorphism, and the
carrier-continuous supported-affine theorem gives its finite PL
certificate on the already triangulated whole domain.
See Hudson 1969, Lemma 2.14, pp. 60--61 and derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- A finite PL compression into its own source glues to
the identity on a compact remainder whenever it fixes the
actual overlap. Only the whole source union needs an explicit
finite triangulation. See Hudson pp. 60--61 and derivation 247. -/
theorem exists_finitePL_union_id_of_fixed_overlap
    {P C R : Set X} (e : P ≃ₜ C) (he : e.IsFinitePL)
    (hR : IsCompact R) (hCP : C ⊆ P)
    (hfix : ∀ x : P, (x : X) ∈ R → (e x : X) = x)
    (K : SimplicialComplex ℝ X) (hK : K.faces.Finite) (hspace : K.space = P ∪ R) :
    ∃ H : (P ∪ R : Set X) ≃ₜ (C ∪ R : Set X), H.IsFinitePL ∧
      (∀ x : P, (H ⟨x, Or.inl x.property⟩ : X) = e x) ∧
      ∀ x : R, (H ⟨x, Or.inr x.property⟩ : X) = x := by
  classical
  obtain ⟨g, hg, hgv⟩ := he
  have hoverlap (x : P) : (x : X) ∈ R ↔ (e x : X) ∈ R := by
    constructor
    · intro hx
      rwa [hfix x hx]
    · intro hx
      let y : P := ⟨e x, hCP (e x).property⟩
      have hey : e y = e x := Subtype.ext (hfix y hx)
      have hyx : y = x := e.injective hey
      exact congrArg Subtype.val hyx ▸ hx
  obtain ⟨H, hHP, hHR⟩ := exists_union_of_compact hg.isCompact hR e
    (Homeomorph.refl R) hoverlap (fun x hxP hxR => hfix ⟨x, hxP⟩ hxR)
  let f : X → X := fun x => if hx : x ∈ P ∪ R then H ⟨x, hx⟩ else x
  have hfv (x : (P ∪ R : Set X)) : f x = (H x : X) := by
    dsimp only [f]
    rw [dif_pos x.property]
  have hgf : EqOn g f P := by
    intro x hx
    exact (hgv ⟨x, hx⟩).symm.trans
      ((hHP ⟨x, hx⟩).symm.trans (hfv ⟨x, Or.inl hx⟩).symm)
  have hfcont : ContinuousOn f (P ∪ R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp H.continuous using 1
    funext x
    exact hfv x
  have hoff (x : X) (hx : x ∈ K.space) (hxP : x ∉ P) : f x = x := by
    have hxR : x ∈ R := (hspace.subset hx).resolve_left hxP
    exact (hfv ⟨x, Or.inr hxR⟩).trans (hHR ⟨x, hxR⟩)
  have hPL := (hg.congr hgf).on_finite_polyhedron_of_continuousOn_eq_affine_off
    K hK (hspace.symm ▸ hfcont) (ContinuousAffineMap.id ℝ X) hoff
  rw [hspace] at hPL
  exact ⟨H, ⟨f, hPL, fun x => (hfv x).symm⟩, hHP, hHR⟩

end Homeomorph
