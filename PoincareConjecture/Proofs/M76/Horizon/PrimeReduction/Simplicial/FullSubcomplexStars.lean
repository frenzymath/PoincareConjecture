import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ClosedSideSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem closedStar_eq_of_retains_closedStar
    (K T : SimplicialComplex ℝ E) (hTK : T ≤ K) (p : E)
    (hstar : K.closedStar p ≤ T) : T.closedStar p = K.closedStar p := by
  ext s
  constructor
  · exact fun hs => ⟨hTK hs.1, hTK hs.2⟩
  · intro hs
    refine ⟨hstar hs, hstar ⟨hs.2, ?_⟩⟩
    simpa only [Finset.insert_idem] using hs.2

theorem link_eq_of_retains_closedStar
    (K T : SimplicialComplex ℝ E) (hTK : T ≤ K) (p : E)
    (hstar : K.closedStar p ≤ T) : T.link p = K.link p := by
  ext s
  constructor
  · exact fun hs => ⟨hTK hs.1, hs.2.1, hTK hs.2.2⟩
  · intro hs
    refine ⟨hstar ⟨hs.1, hs.2.2⟩, hs.2.1, hstar ⟨hs.2.2, ?_⟩⟩
    simpa only [Finset.insert_idem] using hs.2.2

theorem closedStar_space_eq_inter_of_full
    (K P : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hPK : P ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ P.vertices) → s ∈ P.faces)
    {p : E} (hp : p ∈ P.vertices) :
    (P.closedStar p).space = (K.closedStar p).space ∩ P.space := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨space_subset_of_le (K := P.closedStar p) (L := K.closedStar p)
      (fun _ hs => ⟨hPK hs.1, hPK hs.2⟩) hx,
      space_subset_of_le (K := P.closedStar p) (L := P) (fun _ hs => hs.1) hx⟩
  · rintro x ⟨hxstar, hxP⟩
    have hxK : x ∈ K.space := space_subset_of_le hPK hxP
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
    have hsP := K.face_mem_subcomplex_of_intrinsicInterior P hPK hs hxs hxP
    have hsstar := K.face_mem_subcomplex_of_intrinsicInterior (K.closedStar p)
      (fun _ ht => ht.1) hs hxs hxstar
    have hins : insert p s ∈ P.faces := hfull _ hsstar.2 (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hp
      · exact P.down_closed hsP (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v))
    exact (P.closedStar p).convexHull_subset_space ⟨hsP, hins⟩
      (intrinsicInterior_subset hxs)

theorem link_space_eq_inter_of_full
    (K P : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hPK : P ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ P.vertices) → s ∈ P.faces)
    {p : E} (hp : p ∈ P.vertices) :
    (P.link p).space = (K.link p).space ∩ P.space := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨space_subset_of_le (K := P.link p) (L := K.link p)
      (fun _ hs => ⟨hPK hs.1, hs.2.1, hPK hs.2.2⟩) hx,
      space_subset_of_le (K := P.link p) (L := P) (fun _ hs => hs.1) hx⟩
  · rintro x ⟨hxlink, hxP⟩
    have hxK : x ∈ K.space := space_subset_of_le hPK hxP
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
    have hsP := K.face_mem_subcomplex_of_intrinsicInterior P hPK hs hxs hxP
    have hslink := K.face_mem_subcomplex_of_intrinsicInterior (K.link p)
      (fun _ ht => ht.1) hs hxs hxlink
    have hins : insert p s ∈ P.faces := hfull _ hslink.2.2 (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hp
      · exact P.down_closed hsP (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v))
    exact (P.link p).convexHull_subset_space ⟨hsP, hslink.2.1, hins⟩
      (intrinsicInterior_subset hxs)

end Geometry.SimplicialComplex
