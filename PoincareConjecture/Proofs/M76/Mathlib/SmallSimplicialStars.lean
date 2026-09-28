import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem closedFaceStar_subset_closedBall_of_diam_le (K : SimplicialComplex ℝ E)
    {δ : ℝ} (hdiam : ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ δ) (p : E) :
    (K.closedFaceStar {p}).space ⊆ closedBall p δ := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have ht : insert p s ∈ K.faces := by
    simpa only [Finset.singleton_union] using hs.2
  have hxt : x ∈ convexHull ℝ (↑(insert p s) : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert p s)) hxs
  have hpt : p ∈ convexHull ℝ (↑(insert p s) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_self p s)
  exact (dist_le_diam_of_mem
    ((insert p s).finite_toSet.isCompact_convexHull ℝ).isBounded hxt hpt).trans
    (hdiam _ ht)

theorem exists_mesh_for_subdivision_stars (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {ι : Type*} (U : ι → Set K.space)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x : K.space, ∃ i, x ∈ U i) :
    ∃ δ > 0, ∀ L : SimplicialComplex ℝ E, L.IsSubdivision K →
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) ≤ δ) →
      ∀ p : E, {p} ∈ L.faces → ∃ i, ∀ x : K.space,
        (x : E) ∈ (L.closedFaceStar {p}).space → x ∈ U i := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hfinite)
  obtain ⟨r, hr, hLeb⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (univ : Set K.space)) hU (by
      intro x _
      obtain ⟨i, hi⟩ := hcover x
      exact mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨r / 2, half_pos hr, fun L hLK hdiam p hp => ?_⟩
  have hpL : p ∈ L.space := convexHull_subset_space hp (by simp)
  have hpK : p ∈ K.space := hLK.space_eq ▸ hpL
  obtain ⟨i, hi⟩ := hLeb ⟨p, hpK⟩ (mem_univ _)
  refine ⟨i, fun x hx => hi ?_⟩
  change dist (x : E) p < r
  exact (L.closedFaceStar_subset_closedBall_of_diam_le hdiam p hx).trans_lt (half_lt_self hr)

end Geometry.SimplicialComplex
