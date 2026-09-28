import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.RetainedContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.SquareCylinder

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Cyl" => Set.prod (sphere (0 : Fin 2 → ℝ) 1) (Icc (-1 : ℝ) 1)

theorem exists_nested_retained_cylinder_charts
    {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hA₀ : A₀ ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (hA₁ : A₁ ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (henclosing : annulusSquare L d ⊆ B₁.outer.inside)
    (hnested : closure B₁.outer.inside ⊆ B₀.inner.inside)
    (hd : 0 < d) (hwidth : 2 * d < L) :
    let O := annulusSquare L (-d) \ B₀.outer.inside
    let I := closure B₁.inner.inside \ interior (annulusSquare L d)
    ∃ (outer : Cyl ≃ₜ O) (inner : Cyl ≃ₜ I),
      outer.IsFinitePL ∧ inner.IsFinitePL ∧
      O ⊆ squareAnnulus L d ∧ I ⊆ squareAnnulus L d ∧
      (∀ x : Cyl, x.val.2 = -1 ↔ depth L (outer x : P2) = -d) ∧
      (∀ x : Cyl, x.val.2 = 1 ↔ depth L (inner x : P2) = d) ∧
      (∀ x : Cyl, (outer x : P2) ∈ A₀ ↔ x.val.2 = 1) ∧
      (∀ p : squareAnnulus l₀ r₀, (B₀.chart p : P2) ∈ O ↔ depth l₀ p = -r₀) ∧
      (∀ p : squareAnnulus l₁ r₁, (B₁.chart p : P2) ∈ I ↔ depth l₁ p = r₁) ∧
      (∀ x : Cyl, (inner x : P2) ∈ A₁ ↔ x.val.2 = -1) ∧
      (∀ x : Cyl, (outer x : P2) ∈ A₀ ∪ A₁ ↔ x.val.2 = 1) ∧
      (∀ x : Cyl, (inner x : P2) ∈ A₀ ∪ A₁ ↔ x.val.2 = -1) ∧
      (∀ x : O, depth L x < d) ∧ (∀ x : I, -d < depth L x) := by
  dsimp only
  obtain ⟨oa, _, ia, hoa, _, hia, ho0, ho1, _, _, hi0, hi1, _⟩ :=
    exists_nested_essential_collars_retained_annuli B₀ B₁ hA₀ hA₁ henclosing hnested hd hwidth
  obtain ⟨C, hC, hCv⟩ := exists_selected_annulus_cylinder
  let outer := C.symm.trans oa
  let inner := C.symm.trans ia
  have hheight (x : Cyl) : x.val.2 = depth 8 (C.symm x : P2) := by
    simpa only [C.apply_symm_apply] using hCv (C.symm x)
  have hboundO (x : Cyl) : (outer x : P2) ∈ B₀.outer.boundary ℝ ↔ x.val.2 = 1 := by
    rw [hheight]
    exact (ho1 (C.symm x)).symm
  have hboundI (x : Cyl) : (inner x : P2) ∈ B₁.inner.boundary ℝ ↔ x.val.2 = -1 := by
    rw [hheight]
    exact (hi0 (C.symm x)).symm
  have hO := (oriented_collar_retained_contacts B₀ hA₀).1
  have hI := (oriented_collar_retained_contacts B₁ hA₁).2
  have hU := nested_collars_retained_union_contacts B₀ B₁ hA₀ hA₁ hnested
  have henc₀ : annulusSquare L d ⊆ B₀.outer.inside :=
    henclosing.trans (subset_closure.trans (hnested.trans (subset_closure.trans B₀.nested)))
  have hbO := (essential_collar_retained_source_bounds B₀ hA₀ henc₀).1
  have hbI := (essential_collar_retained_source_bounds B₁ hA₁ henclosing).2
  refine ⟨outer, inner, hC.symm.trans hoa, hC.symm.trans hia,
    fun x hx ↦ (hbO x hx).1, fun x hx ↦ (hbI x hx).1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x ↦ (hbO x x.property).2, fun x ↦ (hbI x x.property).2⟩
  · intro x
    rw [hheight]
    exact ho0 (C.symm x)
  · intro x
    rw [hheight]
    exact hi1 (C.symm x)
  · intro x
    exact (show (outer x : P2) ∈ A₀ ↔ (outer x : P2) ∈ B₀.outer.boundary ℝ from
      ⟨fun h ↦ hO.subset ⟨h, (outer x).property⟩, fun h ↦ (hO.symm.subset h).1⟩).trans
        (hboundO x)
  · intro p
    exact (show (B₀.chart p : P2) ∈ annulusSquare L (-d) \ B₀.outer.inside ↔
        (B₀.chart p : P2) ∈ B₀.outer.boundary ℝ from
      ⟨fun h ↦ hO.subset ⟨(B₀.chart p).property, h⟩,
        fun h ↦ (hO.symm.subset h).2⟩).trans (B₀.outer_depth p)
  · intro p
    exact (show (B₁.chart p : P2) ∈ closure B₁.inner.inside \ interior (annulusSquare L d) ↔
        (B₁.chart p : P2) ∈ B₁.inner.boundary ℝ from
      ⟨fun h ↦ hI.subset ⟨(B₁.chart p).property, h⟩,
        fun h ↦ (hI.symm.subset h).2⟩).trans (B₁.inner_depth p)
  · intro x
    exact (show (inner x : P2) ∈ A₁ ↔ (inner x : P2) ∈ B₁.inner.boundary ℝ from
      ⟨fun h ↦ hI.subset ⟨h, (inner x).property⟩, fun h ↦ (hI.symm.subset h).1⟩).trans
        (hboundI x)
  · intro x
    exact (show (outer x : P2) ∈ A₀ ∪ A₁ ↔ (outer x : P2) ∈ B₀.outer.boundary ℝ from
      ⟨fun h ↦ hU.1.subset ⟨h, (outer x).property⟩, fun h ↦ (hU.1.symm.subset h).1⟩).trans
        (hboundO x)
  · intro x
    exact (show (inner x : P2) ∈ A₀ ∪ A₁ ↔ (inner x : P2) ∈ B₁.inner.boundary ℝ from
      ⟨fun h ↦ hU.2.subset ⟨h, (inner x).property⟩, fun h ↦ (hU.2.symm.subset h).1⟩).trans
        (hboundI x)

end PoincareConjecture.M76.Dehn.Annuli
