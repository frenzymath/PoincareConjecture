import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryDualBlockLevel
import PoincareConjecture.Proofs.M76.Wall.Mathlib.SupportingConeLevel

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem binary_vertex_link_levels
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K A : SimplicialComplex ℝ E) [Fintype K.faces] (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hcard : ∀ s ∈ A.faces, s.card ≤ 2)
    {F : E → E} {h : E → ℝ}
    (hF : K.barycentricSubdivision.AffineOnFaces F) (hh : K.AffineOnFaces h)
    (hcenters : ∀ s : K.faces, F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0))
    (hmarks : ∀ L : SimplicialComplex ℝ E, L ≤ K → F '' L.space = L.space)
    {p : E} (hpA : p ∈ A.vertices) :
    (K.barycentricDualBlock {p}).space ∩ {x | h (F x) = (1 / 2 : ℝ)} ⊆
        ((K.barycentricDualBlock {p}).link p).space ∧
      ∀ x ∈ ((K.barycentricDualBlock {p}).link p).space,
        (1 / 2 : ℝ) < h (F x) →
        ∃ s ∈ A.faces, s.card = 2 ∧ p ∈ s ∧
          x ∈ (K.barycentricDualBlock s).space \
            ((K.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  classical
  let N := K.barycentricDualBlock {p}
  let k := h ∘ F
  have hk : K.barycentricSubdivision.AffineOnFaces k :=
    K.subcomplex_preserving_pullback_affineOnFaces K.barycentricSubdivision
      K.barycentricSubdivision_isSubdivision hF hh hmarks
  have hkN : N.AffineOnFaces k := fun s hs => hk s hs.1
  have hpK : p ∈ K.vertices := hAK hpA
  have hapex : k p = 1 := by
    have hc : F p = ({p} : Finset E).binaryFaceCenter A.vertices := by
      simpa only [Finset.centroid_singleton, id_eq] using hcenters ⟨{p}, hpK⟩
    change h (F p) = 1
    rw [hc]
    apply hh.binaryFaceCenter_const hpK A.vertices 1
    intro v hv
    have hvp := Finset.mem_singleton.mp hv
    subst v
    exact (hvalues p hpK).1 hpA
  have hlower (v : E) (hv : v ∈ N.vertices) : (1 / 2 : ℝ) ≤ k v := by
    obtain ⟨s, hs, hps, hsv⟩ := hv.2 v (Finset.mem_singleton_self v)
    rw [← hsv]
    change (1 / 2 : ℝ) ≤ h (F (s.centroid ℝ id))
    rw [hcenters ⟨s, hs⟩]
    exact (hh.half_le_binaryFaceCenter_iff hs A.vertices
      (fun w hw => hvalues w (K.face_subset_vertices hs hw))).mpr
      ⟨p, hps (Finset.mem_singleton_self p), hpA⟩
  have hcone : N.closedStar p = N := by
    simpa only [Finset.centroid_singleton, id_eq] using
      K.barycentricDualBlock_closedStar_faceCentroid hpK
  refine ⟨hkN.supporting_level_subset_link p (1 / 2 : ℝ) hcone
    (by rw [hapex]; norm_num) hlower, ?_⟩
  intro x hx hhigh
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
  have hvertex : ∃ v ∈ t, (1 / 2 : ℝ) < k v := by
    by_contra hn
    obtain ⟨a, ha⟩ := hk t ht.1.1
    have hbound : (t : Set E) ⊆ a ⁻¹' Iic (1 / 2 : ℝ) := by
      intro v hv
      change a v ≤ (1 / 2 : ℝ)
      rw [← ha (subset_convexHull ℝ _ hv)]
      exact le_of_not_gt (fun hvh => hn ⟨v, hv, hvh⟩)
    have hax : a x ≤ (1 / 2 : ℝ) := convexHull_min hbound
      ((convex_Iic (1 / 2 : ℝ)).affine_preimage a.toAffineMap) hxt
    rw [← ha hxt] at hax
    exact (not_le_of_gt hhigh) hax
  obtain ⟨v, hv, hvhigh⟩ := hvertex
  obtain ⟨c, _, hfaces, hchain, htc⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains t).mp ht.1.1
  have hcoface (u : Finset E) (hu : u ∈ c) : ({p} : Finset E) ⊆ u := by
    have hcu : u.centroid ℝ id ∈ t := by
      rw [htc]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    obtain ⟨w, hw, hpw, hwu⟩ := ht.1.2 _ hcu
    have he' : (⟨w, hw⟩ : K.faces) = ⟨u, hfaces u hu⟩ := K.faceCentroid_injective hwu
    have he : w = u := congrArg Subtype.val he'
    exact he ▸ hpw
  have hnot (u : Finset E) (hu : u ∈ c) : u ≠ {p} := by
    intro he
    subst u
    apply ht.2.1
    rw [htc]
    exact Finset.mem_image.mpr ⟨{p}, hu, Finset.centroid_singleton ℝ id p⟩
  have htwo (u : Finset E) (hu : u ∈ c) : 2 ≤ u.card := by
    have hlt := Finset.card_lt_card ((hcoface u hu).ssubset_of_ne (hnot u hu).symm)
    simp only [Finset.card_singleton] at hlt
    omega
  have hv' : v ∈ c.image (fun u => u.centroid ℝ id) := htc ▸ hv
  obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hv'
  have hselected : ∀ w ∈ s, w ∈ A.vertices := by
    intro w hw
    by_contra hwA
    have hmid := hh.binaryFaceCenter_le_half (hfaces s hs) A.vertices
      (fun z hz => hvalues z (K.face_subset_vertices (hfaces s hs) hz)) ⟨w, hw, hwA⟩
    have hkv : k v = h (s.binaryFaceCenter A.vertices) := by
      rw [← hsv]
      change h (F (s.centroid ℝ id)) = h (s.binaryFaceCenter A.vertices)
      rw [hcenters ⟨s, hfaces s hs⟩]
    rw [← hkv] at hmid
    exact (not_le_of_gt hvhigh) hmid
  have hsA : s ∈ A.faces := hfull s (hfaces s hs) hselected
  have hscard : s.card = 2 := le_antisymm (hcard s hsA) (htwo s hs)
  have htJ : t ∈ (K.barycentricDualBlock s).faces := by
    refine ⟨ht.1.1, ?_⟩
    intro z hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp (htc ▸ hz)
    refine ⟨u, hfaces u hu, ?_, huz⟩
    rcases hchain s hs u hu with hsu | hus
    · exact hsu
    · exact (Finset.eq_of_subset_of_card_le hus (by rw [hscard]; exact htwo u hu)).symm.subset
  have hmax : ∀ u ∈ A.faces, s ⊆ u → u = s := by
    intro u hu hsu
    exact (Finset.eq_of_subset_of_card_le hsu (by rw [hscard]; exact hcard u hu)).symm
  have hlevels := K.image_dualBlock_link_binaryLevel A hAK hfull hF hh hcenters
    hvalues hmarks hsA hmax
  refine ⟨s, hsA, hscard, hcoface s hs (Finset.mem_singleton_self p),
    (K.barycentricDualBlock s).convexHull_subset_space htJ hxt, ?_⟩
  intro hxQ
  have he := (hlevels.1.subset ⟨x, hxQ, rfl⟩).2
  exact hhigh.ne' he

end Geometry.SimplicialComplex
