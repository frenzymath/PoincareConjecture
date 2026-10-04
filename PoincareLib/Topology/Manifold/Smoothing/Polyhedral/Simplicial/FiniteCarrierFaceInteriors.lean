import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexIntrinsicFrontier
import Mathlib.Data.Finset.Max

/-!
# Relative-interior faces containing carrier points

Every point of a finite complex belongs to the intrinsic interior of
a containing face of minimum cardinality. See Cairns 1940,
pp. 799, 804--806 and M76 derivations 66, 68.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A minimum containing face puts a carrier point in its
relative interior. See Cairns pp. 799, 804--806 and M76
derivations 66, 68. -/
theorem exists_face_intrinsicInterior_of_finite (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {x : E} (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  let T := hfinite.toFinset.filter (fun s : Finset E => x ∈ convexHull ℝ (s : Set E))
  have hT : T.Nonempty := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact ⟨s, Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr hs, hxs⟩⟩
  obtain ⟨s, hsT, hmin⟩ := T.exists_min_image (fun t => t.card) hT
  obtain ⟨hsK', hxs⟩ := Finset.mem_filter.mp hsT
  have hsK := hfinite.mem_toFinset.mp hsK'
  refine ⟨s, hsK, ?_⟩
  by_contra hnot
  have hfront : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hxs, hnot⟩
  obtain ⟨i, hi, hxi⟩ := ((K.indep hsK).mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces hsK) x).mp hfront
  have hne : (s.erase i).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hxi
  have heK := K.down_closed hsK (Finset.erase_subset i s) hne
  have heT : s.erase i ∈ T :=
    Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr heK, hxi⟩
  have hc := hmin (s.erase i) heT
  have hlt := Finset.card_erase_lt_of_mem hi
  omega

end Geometry.SimplicialComplex
