import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology

/-!
# Identification of two realizations of a disjoint union

Two smooth disjoint unions of exactly the same pieces are diffeomorphic.
The maps are defined on the clopen regions and are smooth by locality.
This is the whole-survivor substitution in MT Corollary 15.4, pp. 358-359.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT
namespace SmoothDisjointUnionData

variable {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {A B : GeneralizedSliceCarrier.{u}}

/-- A point belongs to a unique displayed region of the disjoint union.
Source: the disjoint unions in MT Proposition 15.3, pp. 357-358. -/
theorem existsUnique_region (D : SmoothDisjointUnionData pieces A) (x : A.carrier) :
    ∃! i, x ∈ D.region i := by
  have hx : x ∈ ⋃ i, D.region i := D.cover.symm ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hji
  exact Set.disjoint_left.mp (D.pairwise_disjoint j i hji) hj hi

/-- The displayed region containing a point. Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def regionIndex (D : SmoothDisjointUnionData pieces A) (x : A.carrier) : Fin n :=
  (D.existsUnique_region x).choose

/-- The chosen region contains the point. Source: MT Corollary 15.4, pp. 358-359. -/
theorem mem_regionIndex (D : SmoothDisjointUnionData pieces A) (x : A.carrier) :
    x ∈ D.region (D.regionIndex x) :=
  (D.existsUnique_region x).choose_spec.1

/-- Any region containing a point has the chosen index.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem regionIndex_eq (D : SmoothDisjointUnionData pieces A) {x : A.carrier}
    {i : Fin n} (hx : x ∈ D.region i) : D.regionIndex x = i :=
  ((D.existsUnique_region x).choose_spec.2 i hx).symm

/-- Match two realizations using the inverse and forward maps of their common
piece. Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def identifyMap (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces B) (x : A.carrier) : B.carrier :=
  (E.identify (D.regionIndex x)).map ((D.identify (D.regionIndex x)).inverse x)

/-- On a displayed region the identification has its expected formula.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem identifyMap_eq (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces B) {x : A.carrier} {i : Fin n}
    (hx : x ∈ D.region i) :
    D.identifyMap E x = (E.identify i).map ((D.identify i).inverse x) := by
  obtain rfl := D.regionIndex_eq hx
  rfl

/-- The identification sends each region into its counterpart.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem identifyMap_mem (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces B) {x : A.carrier} {i : Fin n}
    (hx : x ∈ D.region i) : D.identifyMap E x ∈ E.region i := by
  rw [D.identifyMap_eq E hx]
  exact (E.identify i).map_image.subset (Set.mem_image_of_mem _ (Set.mem_univ _))

/-- Matching the regions in the opposite direction is the inverse map.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem identifyMap_left_inverse (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces B) :
    Function.LeftInverse (E.identifyMap D) (D.identifyMap E) := by
  intro x
  have hx := D.mem_regionIndex x
  rw [E.identifyMap_eq D (D.identifyMap_mem E hx), D.identifyMap_eq E hx,
    (E.identify _).left_inverse (Set.mem_univ _), (D.identify _).right_inverse hx]

/-- The matched map is smooth on each open region and hence globally.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem identifyMap_smooth (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces B) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (D.identifyMap E) := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  let i := D.regionIndex x
  refine ⟨D.region i, D.region_open i, D.mem_regionIndex x, ?_⟩
  have h := (E.identify i).map_smooth.comp (D.identify i).inverse_smooth
    (fun _ _ => Set.mem_univ _)
  exact h.congr (fun y hy => D.identifyMap_eq E hy)

/-- Two smooth disjoint unions of the same pieces are diffeomorphic.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def diffeomorph (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces B) :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞ where
  toFun := D.identifyMap E
  invFun := E.identifyMap D
  left_inv := D.identifyMap_left_inverse E
  right_inv := E.identifyMap_left_inverse D
  contMDiff_toFun := D.identifyMap_smooth E
  contMDiff_invFun := E.identifyMap_smooth D

end SmoothDisjointUnionData
end PoincareMT
