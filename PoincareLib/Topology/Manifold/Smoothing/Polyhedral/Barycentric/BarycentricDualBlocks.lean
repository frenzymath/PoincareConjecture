import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricNeighborhoodCarrier

/-!
# The actual geometric dual blocks of finite faces

Retain the barycentric vertices labelled by cofaces of one prescribed
face. The resulting finite subcomplexes have the exact geometric
intersections needed to glue normal products. See Hudson 1969,
pp.8--9, 58--63 and M76 derivation351.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- The closed dual block consists of chains of original cofaces of
the marked face. Its points are the actual barycentric points in the
original ambient space. See Hudson pp.8--9 and derivation351. -/
noncomputable def barycentricDualBlock (s : Finset E) : SimplicialComplex ℝ E :=
  K.barycentricSubdivision.vertexSubcomplex
    {x | ∃ t ∈ K.faces, s ⊆ t ∧ t.centroid ℝ id = x}

/-- Every dual block is a finite subcomplex of the same barycentric
subdivision. See Hudson pp.8--9 and derivation351. -/
theorem barycentricDualBlock_finite (s : Finset E) :
    (K.barycentricDualBlock s).faces.Finite :=
  K.barycentricSubdivision.vertexSubcomplex_finite _ K.barycentricSubdivision_finite

/-- Dual-block faces are faces of the common barycentric subdivision.
See Hudson pp.8--9 and derivation351. -/
theorem barycentricDualBlock_le (s : Finset E) :
    K.barycentricDualBlock s ≤ K.barycentricSubdivision :=
  K.barycentricSubdivision.vertexSubcomplex_le _

/-- Enlarging the marked original face shrinks its actual dual block.
See Hudson pp.8--9 and derivation351. -/
theorem barycentricDualBlock_antitone {s t : Finset E} (hst : s ⊆ t) :
    K.barycentricDualBlock t ≤ K.barycentricDualBlock s := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  intro x hx
  obtain ⟨v, hv, htv, hvx⟩ := hu.2 x hx
  exact ⟨v, hv, hst.trans htv, hvx⟩

/-- Two actual dual blocks meet in precisely the dual block of the
union of their marked faces. This is equality of geometric carriers,
not merely agreement of face labels. See derivation351. -/
theorem barycentricDualBlock_space_inter [DecidableEq E] (s t : Finset E) :
    (K.barycentricDualBlock s).space ∩ (K.barycentricDualBlock t).space =
      (K.barycentricDualBlock (s ∪ t)).space := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
    obtain ⟨b, hb, hxb⟩ := mem_space_iff.mp hy
    have hxi : x ∈ convexHull ℝ ((a ∩ b : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using
        K.barycentricSubdivision.inter_subset_convexHull ha.1 hb.1 ⟨hxa, hxb⟩
    have hne : (a ∩ b).Nonempty := by
      have h := convexHull_nonempty_iff.mp ⟨x, hxi⟩
      exact h
    refine mem_space_iff.mpr ⟨a ∩ b, ⟨?_, ?_⟩, hxi⟩
    · exact K.barycentricSubdivision.down_closed ha.1 Finset.inter_subset_left hne
    · intro y hy
      obtain ⟨u, hu, hsu, huy⟩ := ha.2 y (Finset.mem_inter.mp hy).1
      obtain ⟨v, hv, htv, hvy⟩ := hb.2 y (Finset.mem_inter.mp hy).2
      have huv' : (⟨u, hu⟩ : K.faces) = ⟨v, hv⟩ :=
        K.faceCentroid_injective (huy.trans hvy.symm)
      have huv : u = v := congrArg Subtype.val huv'
      subst v
      exact ⟨u, hu, Finset.union_subset_iff.mpr ⟨hsu, htv⟩, huy⟩
  · intro hx
    obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
    exact ⟨mem_space_iff.mpr ⟨a, K.barycentricDualBlock_antitone
      Finset.subset_union_left ha, hxa⟩,
      mem_space_iff.mpr ⟨a, K.barycentricDualBlock_antitone
        Finset.subset_union_right ha, hxa⟩⟩

/-- A nonempty marked vertex set which is not an original face has
empty dual block. In particular, blocks indexed by incompatible
faces are geometrically disjoint. See derivation351. -/
theorem barycentricDualBlock_space_eq_empty_of_not_face
    {s : Finset E} (hs : s.Nonempty) (hsK : s ∉ K.faces) :
    (K.barycentricDualBlock s).space = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨t, ht, _⟩ := mem_space_iff.mp hx
  obtain ⟨v, hv⟩ := K.barycentricSubdivision.nonempty_of_mem_faces ht.1
  obtain ⟨u, hu, hsu, _⟩ := ht.2 v hv
  exact hsK (K.down_closed hu hsu hs)

/-- Vertex dual blocks cover the whole derived neighborhood of the
actual subcomplex. A least face in each barycentric chain supplies one
common original vertex for that entire fine simplex. See derivation351. -/
theorem barycentricNeighborhood_space_eq_iUnion_dualBlocks
    (L : SimplicialComplex ℝ E) :
    (K.barycentricNeighborhood L).space =
      ⋃ v ∈ L.vertices, (K.barycentricDualBlock {v}).space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains t).mp ht.1
    obtain ⟨s, hs, hmin⟩ := a.exists_min_image Finset.card ha
    have hst (u : Finset E) (hu : u ∈ a) : s ⊆ u := by
      rcases hchain s hs u hu with hsu | hus
      · exact hsu
      · exact (Finset.eq_of_subset_of_card_le hus (hmin u hu)).symm.subset
    have hcs : s.centroid ℝ id ∈ t := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    obtain ⟨r, hr, ⟨v, hvr, hvL⟩, hrs⟩ := ht.2 _ hcs
    have hrs'' : (⟨r, hr⟩ : K.faces) = ⟨s, hfaces s hs⟩ :=
      K.faceCentroid_injective hrs
    have hrs' : r = s := congrArg Subtype.val hrs''
    subst r
    refine mem_iUnion₂.mpr ⟨v, hvL, mem_space_iff.mpr ⟨t, ⟨ht.1, ?_⟩, hxt⟩⟩
    intro y hy
    obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (heq ▸ hy)
    exact ⟨u, hfaces u hu, Finset.singleton_subset_iff.mpr (hst u hu hvr), huy⟩
  · intro hx
    obtain ⟨v, hvL, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    refine mem_space_iff.mpr ⟨t, ⟨ht.1, ?_⟩, hxt⟩
    intro y hy
    obtain ⟨s, hs, hvs, hsy⟩ := ht.2 y hy
    exact ⟨s, hs, ⟨v, hvs (Finset.mem_singleton_self v), hvL⟩, hsy⟩

end Geometry.SimplicialComplex
