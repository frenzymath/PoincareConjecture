import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryDualBlockLevel
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteContactEdgeVertex
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetBoundary

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem image_endpoint_foot_rim_binaryLevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hDK : D ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hfinite : (A.space ∩ D.space).Finite)
    {F : E → E} {h : E → ℝ}
    (hF : K.barycentricSubdivision.AffineOnFaces F) (hh : K.AffineOnFaces h)
    (hcenters : ∀ s : K.faces, F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0))
    (hmarks : ∀ L : SimplicialComplex ℝ E, L ≤ K → F '' L.space = L.space)
    {p : E} (hpA : p ∈ A.vertices) (hpD : p ∈ D.vertices) :
    F '' (((K.barycentricDualBlock {p}).link p).space ∩
        (D.barycentricDualBlock {p}).space) =
      (F '' (D.barycentricDualBlock {p}).space) ∩ {x | h x = (1 / 2 : ℝ)} := by
  classical
  let N := D.barycentricDualBlock {p}
  let k := h ∘ F
  have hk : N.AffineOnFaces k := by
    intro s hs
    exact K.subcomplex_preserving_pullback_affineOnFaces
      K.barycentricSubdivision K.barycentricSubdivision_isSubdivision hF hh hmarks s
      (D.barycentricSubdivision_mono hDK hs.1)
  have hpK : p ∈ K.vertices := hDK hpD
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
  have hother (v : E) (hv : v ∈ N.vertices) (hvp : v ≠ p) : k v = (1 / 2 : ℝ) := by
    obtain ⟨s, hs, hps, hsv⟩ := hv.2 v (Finset.mem_singleton_self v)
    have hp : p ∈ s := hps (Finset.mem_singleton_self p)
    have hnot : s ≠ {p} := by
      intro he
      subst s
      have hpv : p = v := by simpa only [Finset.centroid_singleton, id_eq] using hsv
      exact hvp hpv.symm
    have hneg : ∃ w ∈ s, w ∉ A.vertices := by
      by_contra hn
      push Not at hn
      have hsA : s ∈ A.faces := hfull s (hDK hs) hn
      have hmap : MapsTo id (convexHull ℝ (s : Set E)) (A.space ∩ D.space) :=
        fun _ hx => ⟨A.convexHull_subset_space hsA hx, D.convexHull_subset_space hs hx⟩
      apply hnot
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hp, ?_⟩
      intro w hw
      exact (convex_convexHull ℝ (s : Set E)).isPreconnected.constant_of_mapsTo
        hfinite.isDiscrete continuousOn_id hmap
        (subset_convexHull ℝ _ hw) (subset_convexHull ℝ _ hp)
    rw [← hsv]
    change h (F (s.centroid ℝ id)) = (1 / 2 : ℝ)
    rw [hcenters ⟨s, hDK hs⟩]
    apply hh.binaryFaceCenter_mixed (hDK hs) A.vertices
    · exact ⟨Finset.filter_nonempty_iff.mpr ⟨p, hp, hpA⟩,
        Finset.filter_nonempty_iff.mpr hneg⟩
    · intro w hw
      exact hvalues w (K.face_subset_vertices (hDK hs) hw)
  have hcone : N.closedStar p = N := by
    simpa only [Finset.centroid_singleton, id_eq] using
      D.barycentricDualBlock_closedStar_faceCentroid hpD
  obtain ⟨_, hlevel⟩ := hk.closedStar_link_level p (1 / 2 : ℝ) hcone
    (by rw [hapex]; norm_num) hother
  have hrim : ((K.barycentricDualBlock {p}).link p).space ∩ N.space =
      (N.link p).space := by
    simpa only [inter_comm] using
      (link_space_eq_inter_of_closedStar_eq (K.barycentricDualBlock {p}) N
        (K.barycentricDualBlock_mono_of_subcomplex D hDK {p}) p hcone).symm
  change F '' (((K.barycentricDualBlock {p}).link p).space ∩ N.space) =
    (F '' N.space) ∩ {x | h x = (1 / 2 : ℝ)}
  rw [hrim, hlevel]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxh⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hxh⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxh⟩
    exact ⟨x, ⟨hx, hxh⟩, rfl⟩

end Geometry.SimplicialComplex
