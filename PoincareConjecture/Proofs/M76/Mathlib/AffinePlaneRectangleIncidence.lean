import PoincareConjecture.Proofs.M76.Mathlib.PlanarRectangleRegionIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates










set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem FinitePiecewiseAffineOn.inter_image_rectangle_eq_half_in_plane
    {f : (ℝ × ℝ) → E} {r : ℝ} (hr : 0 < r)
    (hf : FinitePiecewiseAffineOn f (base r)) (hinj : InjOn f (base r))
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hdplane : d ⊆ {x | A x = 0})
    (hfplane : MapsTo f (base r) {x | A x = 0})
    (hrim : ∀ x ∈ base r, f x ∈ q ↔ x.2 = 0) :
    d ∩ (f '' base r) = f '' (Icc (-r) r ×ˢ Icc (-r) 0) ∨
      d ∩ (f '' base r) = f '' (Icc (-r) r ×ˢ Icc 0 r) := by
  obtain ⟨a, R, _, hleft, _⟩ := A.exists_zeroLevel_coordinates (F := ℝ × ℝ) hA
    (by simpa [Module.finrank_prod] using hdim)
  have hR : InjOn R {x | A x = 0} := hleft.injOn
  have hdf := hd.affine_image R (hR.mono hdplane)
  have hfinj : InjOn (R ∘ f) (base r) := by
    intro x hx y hy heq
    exact hinj hx hy (hR (hfplane hx) (hfplane hy) heq)
  have hfront : ∀ x ∈ base r, (R ∘ f) x ∈ frontier (R '' d) ↔ x.2 = 0 := by
    intro x hx
    rw [hdf.frontier_eq_of_finrank_eq rfl]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyf : y = f x := hR (hdplane (hd.1 hy)) (hfplane hx) heq
      exact (hrim x hx).mp (hyf ▸ hy)
    · intro hx0
      exact ⟨f x, (hrim x hx).mpr hx0, rfl⟩
  have hresult := (hf.postcomp R).inter_image_rectangle_eq_half hr hfinj
    hdf.isCompact.isClosed (hdf.closure_interior_of_finrank_eq rfl) hfront
  have himage : f '' base r ⊆ {x | A x = 0} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfplane hx
  have hcancel (T : Set (ℝ × ℝ)) (hT : T ⊆ base r)
      (h : (R '' d) ∩ ((R ∘ f) '' base r) = (R ∘ f) '' T) :
      d ∩ (f '' base r) = f '' T := by
    apply (hR.image_eq_image_iff (inter_subset_left.trans hdplane)
      ((image_mono hT).trans himage)).mp
    rw [hR.image_inter hdplane himage, image_image, image_image]
    exact h
  rcases hresult with h | h
  · exact Or.inl (hcancel _
      (fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans hr.le⟩) h)
  · exact Or.inr (hcancel _
      (fun _ hx => ⟨hx.1, (neg_nonpos.mpr hr.le).trans hx.2.1, hx.2.2⟩) h)

end Geometry
