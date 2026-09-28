import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CappedCylinder



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
private instance : ChartedSpace (E1 × Real) (S1 × Real) := prodChartedSpace E1 S1 Real Real





theorem exists_ambient_filling_of_capped_regular_annulus
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) {a b δ w : Real}
    (hδ : 0 < δ) (hw : 0 < w) (hsep : a + w < b - w)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : T.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hT : ContMDiffOn Iprod (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target)
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) → inner Real v (f (T (q, t))) = t)
    (hleft : ∀ t ∈ Icc a (a + w),
      range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, t)))) =
        range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, a)))))
    (hright : ∀ t ∈ Icc (b - w) b,
      range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, t)))) =
        range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, b)))))
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 =
      range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, a)))))
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 =
      range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (T (q, b)))))
    (u z : Real) (hu : 0 < u) (hz : 0 < z) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A ''
          boundedCylinderNorthernCap v) ∪
        (f '' (T '' (univ ×ˢ Icc a b))) ∪
        (liftPlaneDiffeomorph hv b z hz.ne' B '' boundedCylinderNorthernCap v) := by
  obtain ⟨Q, hQ, D, _, hDlow, hDupper, _, hDband⟩ :=
    exists_actual_band_flattening_with_constant_ends hf hv hδ hw hsep T
      hsource hT hTi hheight hleft hright
  have hab : a < b := by linarith
  have hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 =
      (B.trans Q) '' sphere (0 : Hemisphere.Plane v) 1 := by
    change A '' sphere (0 : Hemisphere.Plane v) 1 =
      (Q ∘ B) '' sphere (0 : Hemisphere.Plane v) 1
    rw [image_comp, hB, hQ, hA]
  obtain ⟨G, hG⟩ := exists_ambient_capped_cylinder_of_two_fillings
    hv a b hab u z hu hz A (B.trans Q) hboundary
  let L := liftPlaneDiffeomorph hv a (-u) (neg_ne_zero.mpr hu.ne') A ''
    boundedCylinderNorthernCap v
  let N := f '' (T '' (univ ×ˢ Icc a b))
  let U := liftPlaneDiffeomorph hv b z hz.ne' B '' boundedCylinderNorthernCap v
  have hDL : D '' L = L := image_lower_cap_of_fixed_lower_halfSpace
    hv (show a ≤ a + w / 4 by linarith) hu A D hDlow
  have hDU : D '' U = liftPlaneDiffeomorph hv b z hz.ne' (B.trans Q) ''
      boundedCylinderNorthernCap v := image_upper_cap_of_constant_plane_action
    hv (show b - w / 4 ≤ b by linarith) hz B Q D hDupper
  have hDN : D '' N =
      (fun p : Real × Hemisphere.Plane v => p.1 • v + (A p.2 : E3)) ''
        (Icc a b ×ˢ sphere (0 : Hemisphere.Plane v) 1) := by
    rw [hDband, ← hA]
    ext x
    constructor
    · rintro ⟨⟨t, y⟩, ⟨ht, y', hy', rfl⟩, rfl⟩
      exact ⟨(t, y'), ⟨ht, hy'⟩, rfl⟩
    · rintro ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
      exact ⟨(t, A y), ⟨ht, y, hy, rfl⟩, rfl⟩
  refine ⟨G.trans D.symm, ?_⟩
  apply D.injective.image_injective
  change D '' ((D.symm ∘ G) '' sphere (0 : E3) 1) = D '' (L ∪ N ∪ U)
  rw [image_comp, image_image]
  simp only [D.apply_symm_apply, image_id']
  rw [image_union, image_union, hDL, hDN, hDU]
  exact hG

end Poincare.Manifold.Schoenflies
