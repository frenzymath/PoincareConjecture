import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualEdgeDisk
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.DerivedStarIntersections

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem link_space_eq_inter_of_closedStar_eq
    (K L : SimplicialComplex ℝ E) (hLK : L ≤ K) (p : E)
    (hstar : L.closedStar p = L) :
    (L.link p).space = L.space ∩ (K.link p).space := by
  ext x
  constructor
  · intro hx
    have hsource : L.link p ≤ L := fun _ ht => ht.1
    have htarget : L.link p ≤ K.link p :=
      fun _ ht => ⟨hLK ht.1, ht.2.1, hLK ht.2.2⟩
    exact ⟨space_subset_of_le hsource hx, space_subset_of_le htarget hx⟩
  · intro hx
    obtain ⟨t, htL, htK, hxt⟩ := K.exists_common_face_of_mem_subcomplexes
      L (K.link p) hLK (fun _ ht => ht.1) hx
    have htstar : t ∈ (L.closedStar p).faces := hstar.symm ▸ htL
    exact (L.link p).convexHull_subset_space ⟨htL, htK.2.1, htstar.2⟩ hxt

variable (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [DecidableEq E] in

theorem barycentricDualBlock_mono_of_subcomplex
    (L : SimplicialComplex ℝ E) [Fintype L.faces] (hLK : L ≤ K) (s : Finset E) :
    L.barycentricDualBlock s ≤ K.barycentricDualBlock s := by
  intro t ht
  refine ⟨L.barycentricSubdivision_mono hLK ht.1, ?_⟩
  intro x hx
  obtain ⟨u, hu, hsu, hux⟩ := ht.2 x hx
  exact ⟨u, hLK hu, hsu, hux⟩

theorem barycentricDualBlock_link_space_of_paired_facet
    {n : ℕ} (hcard : ∀ v ∈ K.faces, v.card ≤ n + 1)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hscard : s.card = n) (htcard : t.card = n + 1) (hucard : u.card = n + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u)
    (hcofaces : ∀ v ∈ K.faces, s ⊆ v → v.card = n + 1 → v = t ∨ v = u) :
    ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space =
      {t.centroid ℝ id, u.centroid ℝ id} := by
  classical
  let N := K.barycentricDualBlock s
  let c : Finset E → E := fun v => v.centroid ℝ id
  have hcinj {v w : Finset E} (hv : v ∈ K.faces) (hw : w ∈ K.faces)
      (he : c v = c w) : v = w := by
    have h : (⟨v, hv⟩ : K.faces) = ⟨w, hw⟩ := K.faceCentroid_injective he
    exact congrArg Subtype.val h
  have hmark (v : Finset E) (hv : v ∈ K.faces) (hsv : s ⊆ v)
      (hvc : v.card = n + 1) : c v ∈ (N.link (c s)).space := by
    have hvertex : c v ∈ N.vertices := by
      refine ⟨(K.mem_barycentricSubdivision_vertices_iff _).mpr ⟨v, hv, rfl⟩, ?_⟩
      intro x hx
      exact ⟨v, hv, hsv, (Finset.mem_singleton.mp hx).symm⟩
    have hstar : ({c v} : Finset E) ∈ (N.closedStar (c s)).faces :=
      (K.barycentricDualBlock_closedStar_faceCentroid hs).symm ▸ hvertex
    apply vertices_subset_space
    refine ⟨hvertex, ?_, hstar.2⟩
    intro h
    have he := hcinj hs hv (Finset.mem_singleton.mp h)
    rw [he] at hscard
    omega
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hfaces, hchain, hfa⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains f).mp hf.1.1
    have hcoface (v : Finset E) (hv : v ∈ a) : s ⊆ v := by
      obtain ⟨w, hw, hsw, hwv⟩ := hf.1.2 _
        (hfa.symm ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      exact hcinj hw (hfaces v hv) hwv ▸ hsw
    have hsize (v : Finset E) (hv : v ∈ a) : v.card = n + 1 := by
      have hne : s ≠ v := by
        intro h
        apply hf.2.1
        rw [hfa]
        exact Finset.mem_image.mpr ⟨v, hv, congrArg c h.symm⟩
      have hlt := Finset.card_lt_card ((hcoface v hv).ssubset_of_ne hne)
      have hle := hcard v (hfaces v hv)
      omega
    obtain ⟨v, hv⟩ := ha
    have hsame (w : Finset E) (hw : w ∈ a) : w = v := by
      rcases hchain w hw v hv with h | h
      · exact Finset.eq_of_subset_of_card_le h (by rw [hsize w hw, hsize v hv])
      · exact (Finset.eq_of_subset_of_card_le h (by rw [hsize w hw, hsize v hv])).symm
    have hsub : (f : Set E) ⊆ {c v} := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hfa ▸ hy)
      exact congrArg c (hsame w hw)
    have hxv : x = c v := by
      simpa only [convexHull_singleton, mem_singleton_iff] using convexHull_mono hsub hxf
    rcases hcofaces v (hfaces v hv) (hcoface v hv) (hsize v hv) with he | he
    · exact Or.inl (hxv.trans (congrArg c he))
    · exact Or.inr (hxv.trans (congrArg c he))
  · rintro (rfl | rfl)
    · exact hmark t ht hst htcard
    · exact hmark u hu hsu hucard

end Geometry.SimplicialComplex
