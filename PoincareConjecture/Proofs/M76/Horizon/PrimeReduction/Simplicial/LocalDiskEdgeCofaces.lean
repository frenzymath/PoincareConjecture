import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.MarkedDiskRefinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.OpenSubcomplexCofaces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.SubdivisionEdgeCofaces
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem ncard_triangle_cofaces_eq_two_of_local_disk
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2)
    {p : E} (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {d q : Set E} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d q)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ q)
    (hopen : IsOpen ((Subtype.val : K.space → E) ⁻¹' (d \ q))) :
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
  classical
  obtain ⟨R, D, A, g, hR, hRK, hDR, hDs, hAR, hAs, hgR, hgi, hgint⟩ :=
    K.exists_marked_disk_face_refinement hK hd hdK hs
  obtain ⟨x, hxs, hxnot, hxd⟩ :=
    K.exists_edge_interior_point_avoiding_vertices R hR hs hs2 hp hopen hpd
  have hxA : x ∈ A.space := hAs.symm.subset (intrinsicInterior_subset hxs)
  obtain ⟨r, hrA, hxr⟩ := A.exists_face_intrinsicInterior_of_finite
    (hR.subset hAR) hxA
  have hr : r ∈ R.faces := hAR hrA
  have hrsub : convexHull ℝ (r : Set E) ⊆ convexHull ℝ (s : Set E) :=
    (A.convexHull_subset_space hrA).trans hAs.subset
  have hrle : r.card ≤ 2 := by
    have h := (R.indep hr).card_le_card_of_subset_affineSpan
      ((subset_convexHull ℝ (r : Set E)).trans
        (hrsub.trans (convexHull_subset_affineSpan (s := (s : Set E)))))
    omega
  have hrpos : 0 < r.card := Finset.card_pos.mpr (R.nonempty_of_mem_faces hr)
  have hrone : r.card ≠ 1 := by
    intro hc
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    have hxv : x = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hxr
    exact hxnot (hxv.symm ▸ (show v ∈ R.vertices from hr))
  have hr2 : r.card = 2 := by omega
  have hxR : x ∈ R.space := R.convexHull_subset_space hr (intrinsicInterior_subset hxr)
  have hopenR : IsOpen ((Subtype.val : R.space → E) ⁻¹' (d \ q)) :=
    hopen.preimage (Homeomorph.setCongr hRK.space_eq).continuous
  have hnear : (Subtype.val ⁻¹' D.space : Set R.space) ∈ 𝓝 (⟨x, hxR⟩ : R.space) :=
    Filter.mem_of_superset (hopenR.mem_nhds hxd)
      (fun y hy => hDs.symm.subset hy.1)
  have hcoface (t : Finset E) (ht : t ∈ R.faces) (hrt : r ⊆ t) : t ∈ D.faces :=
    R.coface_mem_of_subcomplex_mem_nhds D hDR hr ⟨x, hxR⟩ hxr hnear ht hrt
  have hrD : r ∈ D.faces := hcoface r hr Finset.Subset.rfl
  have hgD : D.AffineOnFaces g := fun t ht => hgR t (hDR ht)
  let N := hgD.embeddedImage hgi
  have hN : N.faces.Finite := hgD.embeddedImage_finite hgi (hR.subset hDR)
  have hrN : r.image g ∈ N.faces :=
    (hgD.image_mem_embeddedImage_iff hgi (D.subset_space hrD)).mpr hrD
  have hcard : (r.image g).card = Module.finrank ℝ (Fin 2 → ℝ) := by
    rw [Finset.card_image_iff.mpr (hgi.mono (D.subset_space hrD)), hr2]
    simp
  have hgxr : g x ∈ convexHull ℝ (r.image g : Set (Fin 2 → ℝ)) := by
    rw [Finset.coe_image, ← hgD.image_convexHull hrD]
    exact mem_image_of_mem g (intrinsicInterior_subset hxr)
  have hgxint : g x ∈ interior N.space := by
    rw [hgD.embeddedImage_space hgi]
    exact hgint x hxd
  have hcount := N.faceLink_ncard_eq_two_of_hull_meets_interior
    hN hrN hcard ⟨g x, hgxr, hgxint⟩
  rw [hgD.ncard_embeddedImage_faceLink hgi hrD,
    D.ncard_faceLink_vertices_eq_cofaces, hr2] at hcount
  have hsets : {t : Finset E | t ∈ R.faces ∧ t.card = 3 ∧ r ⊆ t} =
      {t : Finset E | t ∈ D.faces ∧ t.card = 3 ∧ r ⊆ t} := by
    ext t
    exact ⟨fun ht => ⟨hcoface t ht.1 ht.2.2, ht.2⟩,
      fun ht => ⟨hDR ht.1, ht.2⟩⟩
  rw [hRK.ncard_triangle_cofaces_eq_of_shared_edge_interior hR hbound hs hs2 hr hr2
    hxs hxr, hsets]
  exact hcount

end Geometry.SimplicialComplex
