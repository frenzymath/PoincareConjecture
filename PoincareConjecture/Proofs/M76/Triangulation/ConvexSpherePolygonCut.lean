import PoincareConjecture.Proofs.M76.Triangulation.ConvexSpherePolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionInPLChart










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem isFinitePLBallPair_convex_sphere_complement (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    {D : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ))
    (hDs : D ⊆ frontier s)
    (hint : interior ((Subtype.val : frontier s → E) ⁻¹' D) =
      (Subtype.val : frontier s → E) ⁻¹' (D \ P.boundary ℝ))
    (hout : (frontier s \ D).Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) (frontier s \ (D \ P.boundary ℝ)) (P.boundary ℝ) := by
  let A := frontier s \ (D \ P.boundary ℝ)
  let U := frontier s \ D
  have hAS : A ⊆ frontier s := sdiff_subset
  have hUS : U ⊆ frontier s := sdiff_subset
  have hAD : (Subtype.val : frontier s → E) ⁻¹' A =
      ((Subtype.val : frontier s → E) ⁻¹' (D \ P.boundary ℝ))ᶜ := by
    ext x
    simp only [A, mem_preimage, mem_sdiff, mem_compl_iff, x.property, true_and]
  have hUD : (Subtype.val : frontier s → E) ⁻¹' U =
      ((Subtype.val : frontier s → E) ⁻¹' D)ᶜ := by
    ext x
    simp only [U, mem_preimage, mem_sdiff, mem_compl_iff, x.property, true_and]
  have hO : IsOpen ((Subtype.val : frontier s → E) ⁻¹' (D \ P.boundary ℝ)) :=
    hint ▸ isOpen_interior
  have hAc : IsCompact A := by
    let : CompactSpace (frontier s) := isCompact_iff_compactSpace.mp
      (hs.of_isClosed_subset isClosed_frontier hs.isClosed.frontier_subset)
    have hclosed : IsClosed ((Subtype.val : frontier s → E) ⁻¹' A) := by
      rw [hAD]
      exact hO.isClosed_compl
    have hc := hclosed.isCompact.image continuous_subtype_val
    rwa [image_preimage_eq_of_subset (by simpa using hAS)] at hc
  have hUclS : closure ((Subtype.val : frontier s → E) ⁻¹' U) =
      (Subtype.val : frontier s → E) ⁻¹' A := by
    rw [hUD, closure_compl, hint, ← hAD]
  have hUcl : closure U = A :=
    isClosed_frontier.closure_eq_of_preimage_val hUS hAS hUclS
  have hAintS : interior ((Subtype.val : frontier s → E) ⁻¹' A) =
      (Subtype.val : frontier s → E) ⁻¹' U := by
    rw [hAD, interior_compl, hD.closure_preimage_sdiff hDs, ← hUD]
  have hbound : A \ U = P.boundary ℝ := by
    ext x
    simp only [A, U, mem_sdiff]
    have hBD := @hD.1 x
    have hDS := @hDs x
    tauto
  obtain ⟨r, hr⟩ := hD.sdiff_nonempty
  let pole : frontier s := ⟨r, hDs hr.1⟩
  have hAr : (pole : E) ∉ A := fun hx => hx.2 hr
  obtain ⟨d, q, hd, hds, hAd, _, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK hs hcv hne hspace
      (F := ℝ × ℝ) (by simpa [Module.finrank_prod] using hdim) pole hAc hAS hAr
  have hAintd : interior ((Subtype.val : d → E) ⁻¹' A) =
      (Subtype.val : d → E) ⁻¹' U := by
    rw [interior_preimage_val_inclusion_of_open_neighborhood hds hopen hAd sdiff_subset,
      hAintS]
    rfl
  exact hd.of_polygon_region P hP hinj hAc hAd hUcl hAintd hbound hout





theorem exists_convex_sphere_polygon_cut (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = 3) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ frontier s) (p : frontier s)
    (hp : (p : E) ∉ P.boundary ℝ) :
    ∃ D A : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) A (P.boundary ℝ) ∧ D ∪ A = frontier s ∧
      D ∩ A = P.boundary ℝ ∧ (p : E) ∈ A \ P.boundary ℝ := by
  obtain ⟨D, hD, hDs, hpD, hint⟩ := K.exists_convex_sphere_polygon_disk_with_interior
    hK hs hcv hne hspace hdim P hP hinj hPsub p hp
  have hA := K.isFinitePLBallPair_convex_sphere_complement hK hs hcv hne hspace hdim
    P hP hinj hD hDs hint ⟨p, p.property, hpD⟩
  refine ⟨D, frontier s \ (D \ P.boundary ℝ), hD, hA, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_union, mem_sdiff]
    have hDS := @hDs x
    tauto
  · ext x
    simp only [mem_inter_iff, mem_sdiff]
    have hBD := @hD.1 x
    have hDS := @hDs x
    tauto
  · exact ⟨⟨p.property, fun hx => hpD hx.1⟩, hp⟩

end Geometry.SimplicialComplex
