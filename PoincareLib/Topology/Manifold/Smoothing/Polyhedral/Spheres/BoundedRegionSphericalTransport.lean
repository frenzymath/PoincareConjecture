import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLTransport

/-!+# Finite PL transport on a polyhedral spherical completion

An ambient deformation preserving a containing polyhedron extends
by the identity in one extra coordinate. It preserves the cylinder
frontier and exactly transports its complementary-side expressions.
For a compact convex cylinder this is a polyhedral spherical model.
See Alexander 1924, p. 7 and M76 derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- Universal finite-polyhedron PL regularity survives product
with an identity map. Project the compact carrier, compose on a
finite neighborhood of its projection, and append the unchanged
affine coordinate. See Alexander p. 7 and derivation 247. -/
theorem finitePL_prod_refl_on_finite_polyhedron (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space)
    (L : SimplicialComplex ℝ (E × F)) (hL : L.faces.Finite) :
    FinitePiecewiseAffineOn (H.prodCongr (Homeomorph.refl F) : E × F → E × F)
      L.space := by
  let a : E × F →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E F).toContinuousAffineMap
  have hcompact : IsCompact (a '' L.space) :=
    (L.isCompact_space_of_finite hL).image a.continuous
  obtain ⟨K, hK, hprojK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hcompact
      isOpen_univ (subset_univ _)
  have hfirst : FinitePiecewiseAffineOn (H ∘ a) L.space :=
    (hH K hK).comp ((L.affineOnFaces_affine a).finitePiecewiseAffineOn hL)
      (fun x hx => interior_subset (hprojK (mem_image_of_mem a hx)))
  obtain ⟨R, hR, hRL, hfaces⟩ := hfirst
  refine ⟨R, hR, hRL, fun s hs => ?_⟩
  obtain ⟨b, hb⟩ := hfaces s hs
  refine ⟨b.prod (ContinuousLinearMap.snd ℝ E F).toContinuousAffineMap, ?_⟩
  intro x hx
  exact congrArg (fun y : E => (y, x.2)) (hb hx)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Fixing the complement of a set forces an ambient
homeomorphism to preserve the whole set. This supplies the
containing-polyhedron condition for supported deformations.
See Alexander p. 7 and M76 derivation 247. -/
theorem image_eq_self_of_eqOn_compl (H : E ≃ₜ E) {C : Set E}
    (hfix : EqOn H id Cᶜ) : H '' C = C := by
  have hcompl : (H '' C)ᶜ = Cᶜ :=
    (H.image_compl C).symm.trans hfix.image_eq_self
  simpa only [compl_compl] using congrArg (fun s : Set E => sᶜ) hcompl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The product extension preserves the exact cylinder
frontier when the original map preserves its base. Convexity
is not needed for this carrier identity. See derivation 247. -/
theorem image_prod_frontier_of_image_eq (H : E ≃ₜ E) {C : Set E}
    (hC : H '' C = C) (D : Set F) :
    H.prodCongr (Homeomorph.refl F) '' frontier (C ×ˢ D) = frontier (C ×ˢ D) := by
  have hprod : H.prodCongr (Homeomorph.refl F) '' (C ×ˢ D) = C ×ˢ D := by
    change Prod.map H id '' (C ×ˢ D) = C ×ˢ D
    rw [prodMap_image_prod, hC, image_id]
  exact ((H.prodCongr (Homeomorph.refl F)).image_frontier (C ×ˢ D)).trans
    (congrArg frontier hprod)

omit [FiniteDimensional ℝ F] in
/-- The actual product map restricts to a finite PL
self-homeomorphism of the finite cylinder frontier, with its
values on every face retained. See Alexander p. 7 and
M76 derivation 247. -/
theorem exists_finitePL_cylinder_frontier_homeomorph (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space)
    {C : Set E} (hC : H '' C = C) (D : Set F)
    (L : SimplicialComplex ℝ (E × F)) (hL : L.faces.Finite)
    (hLs : L.space = frontier (C ×ˢ D)) :
    ∃ G : frontier (C ×ˢ D) ≃ₜ frontier (C ×ˢ D), G.IsFinitePL ∧
      ∀ x, (G x : E × F) = (H (x : E × F).1, (x : E × F).2) := by
  let P := H.prodCongr (Homeomorph.refl F)
  have hPs : P '' frontier (C ×ˢ D) = frontier (C ×ˢ D) :=
    H.image_prod_frontier_of_image_eq hC D
  have hP : (P.image (frontier (C ×ˢ D))).IsFinitePL := by
    refine ⟨P, ?_, fun _ => rfl⟩
    rw [← hLs]
    exact H.finitePL_prod_refl_on_finite_polyhedron hH L hL
  let G := (P.image (frontier (C ×ˢ D))).trans (Homeomorph.setCongr hPs)
  exact ⟨G, hP.setCongr rfl hPs, fun _ => rfl⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The product extension commutes exactly with the affine
embedding into any fixed horizontal face. This applies to the
surface, cap and either chosen region. See derivation 247. -/
theorem image_prod_refl_face_image (H : E ≃ₜ E) (z : F) (s : Set E) :
    H.prodCongr (Homeomorph.refl F) '' ((fun x : E => (x, z)) '' s) =
      (fun x : E => (x, z)) '' (H '' s) := by
  rw [image_image, image_image]
  rfl

/-- Finite PL ball assertions for the exact complementary
closed side in a cylinder frontier are preserved by the actual
ambient deformation. In the spherical application the original
region and surface lie in the interior of the top face. This
adapter transports a ball certificate; it does not assume an
unbounded Euclidean exterior is a ball. See Alexander p. 7 and
M76 derivation 247. -/
theorem isFinitePLBallPair_cylinderComplement_image_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : E ≃ₜ E)
    (hH : ∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
      FinitePiecewiseAffineOn (H : E → E) K.space)
    {C : Set E} (hC : H '' C = C) (D : Set F) (z : F) (U S : Set E) :
    IsFinitePLBallPair V
        (frontier (C ×ˢ D) \ (fun x : E => (x, z)) '' (H '' U))
        ((fun x : E => (x, z)) '' (H '' S)) ↔
      IsFinitePLBallPair V (frontier (C ×ˢ D) \ (fun x : E => (x, z)) '' U)
        ((fun x : E => (x, z)) '' S) := by
  let P := H.prodCongr (Homeomorph.refl F)
  have hP : ∀ (L : SimplicialComplex ℝ (E × F)), L.faces.Finite →
      FinitePiecewiseAffineOn (P : E × F → E × F) L.space :=
    H.finitePL_prod_refl_on_finite_polyhedron hH
  have hcarrier : P '' (frontier (C ×ˢ D) \ (fun x : E => (x, z)) '' U) =
      frontier (C ×ˢ D) \ (fun x : E => (x, z)) '' (H '' U) := by
    rw [image_sdiff P.injective, H.image_prod_frontier_of_image_eq hC D,
      H.image_prod_refl_face_image]
  have hboundary : P '' ((fun x : E => (x, z)) '' S) =
      (fun x : E => (x, z)) '' (H '' S) := H.image_prod_refl_face_image z S
  rw [← hcarrier, ← hboundary]
  constructor
  · intro hball
    have hpre := hball.preimage_of_finitePL_on_finite_polyhedra P hP
    simpa only [P.preimage_image] using hpre
  · intro hball
    exact hball.image_of_finitePL_on_finite_polyhedra P hP

end Homeomorph
