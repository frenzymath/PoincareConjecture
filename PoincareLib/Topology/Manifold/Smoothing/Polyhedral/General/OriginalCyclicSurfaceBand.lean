import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.OriginalBoxProductCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Collars.OriginalCyclicCollarNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.OriginalSurfaceBandRestriction

/-!
# The complete original surface band in one finite PL product

The actual cyclic box family glues on its original physical
core. Its ambient neighborhood covers a whole compact surface
band, and the same map restricts to that entire band with its
numerical height and fixed original core retained.
See Alexander 1924, pp. 6--8, Hudson 1969, pp. 12--19,
60--61 and M76 derivations 286at, 286av, 286ax.
-/

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

/-- The actual common cyclic family supplies a finite PL
product of the unchanged whole polygon and a positive closed
height interval onto the complete original compact surface
band. The original zero section is fixed pointwise.
See Alexander pp. 6--8 and M76 derivation 286ax. -/
theorem exists_original_cyclic_surface_band
    (P : Polygon E (n + 3)) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → E)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    {r : ℝ} (hr : 0 < r)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (box r))
    (hinj : ∀ i, InjOn (F i) (box r))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-r) r) ×ˢ {0}) = P.cutArc t i)
    (hlateral : ∀ i (j : Bool) u z, u ∈ Icc (-r) r → z ∈ Icc (-r) r →
      F i ((u, if j then r else -r), z) =
        f (if j then finRotate (n + 3) i else i) ((u, 0), z))
    (hcontact : ∀ i, (F i '' box r) ∩ (F (finRotate (n + 3) i) '' box r) =
      f (finRotate (n + 3) i) '' ((Icc (-r) r ×ˢ {0}) ×ˢ Icc (-r) r))
    (hdisjoint : ∀ i j, i ≠ j → finRotate (n + 3) i ≠ j → finRotate (n + 3) j ≠ i →
      Disjoint (F i '' box r) (F j '' box r))
    {S : Set E} (hS : IsCompact S) (A : E → ℝ) (c : ℝ) (hA : ContinuousOn A S)
    (hsection : S ∩ {x | A x = c} = P.boundary ℝ)
    (hheight : ∀ i x, x ∈ box r → A (F i x) = c + x.1.1)
    (hsurface : ∀ i x, x ∈ box r → (F i x ∈ S ↔ x.2 = 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : δ ∈ Ioo 0 ε), δ < r ∧
      ∃ C : (P.boundary ℝ ×ˢ Icc (-δ) δ : Set (E × ℝ)) ≃ₜ
          (S ∩ {x | |A x - c| ≤ δ} : Set E),
        C.IsFinitePL ∧ (∀ p, A (C p) = c + (p : E × ℝ).2) ∧
        ∀ (x : E) (hx : x ∈ P.boundary ℝ),
          (C ⟨(x, 0), ⟨hx, neg_nonpos.mpr hδ.1.le, hδ.1.le⟩⟩ : E) = x := by
  obtain ⟨e, he, heinverse⟩ := P.exists_original_cyclic_product_collar t ht F
    (fun i => f i) hr hF hinj hcore hlateral hcontact hdisjoint
  obtain ⟨heheight, hesurface, hecore⟩ :=
    e.original_box_product_coordinates F heinverse A c hheight hsurface
  have hneighborhood := P.boundary_subset_interior_original_cyclic_boxes t ht F f
    hr hF hinj hcore hlateral hcontact
  obtain ⟨δ, hδ, hband⟩ := P.exists_surface_band_subset_original_neighborhood
    hS isOpen_interior hneighborhood A c hA hsection (lt_min hr hε)
  have hδr : δ < r := hδ.2.trans_le (min_le_left _ _)
  have hδε : δ < ε := hδ.2.trans_le (min_le_right _ _)
  obtain ⟨C, hC, hCheight, hCvalue⟩ := he.exists_original_surface_band_product
    hr ⟨hδ.1.le, hδr.le⟩ A heheight hesurface (hband.trans interior_subset)
  refine ⟨δ, ⟨hδ.1, hδε⟩, hδr, C, hC, hCheight, ?_⟩
  intro x hx
  rw [hCvalue]
  exact hecore _ rfl

end Polygon
