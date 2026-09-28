import PoincareConjecture.Proofs.M38.RegionEquivalences

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {A B : GeneralizedSliceCarrier.{u}}

noncomputable def unionRegionIndex (U : SmoothDisjointUnionData pieces A)
    (x : A.carrier) : Fin n :=
  Classical.choose (Set.mem_iUnion.mp (U.cover.symm ▸ Set.mem_univ x))

theorem unionRegionIndex_mem (U : SmoothDisjointUnionData pieces A) (x : A.carrier) :
    x ∈ U.region (unionRegionIndex U x) :=
  Classical.choose_spec (Set.mem_iUnion.mp (U.cover.symm ▸ Set.mem_univ x))

theorem unionRegionIndex_eq (U : SmoothDisjointUnionData pieces A)
    {x : A.carrier} {i : Fin n} (hx : x ∈ U.region i) : unionRegionIndex U x = i := by
  by_contra hne
  exact Set.disjoint_left.mp (U.pairwise_disjoint _ i hne) (unionRegionIndex_mem U x) hx

noncomputable def unionComparisonMap (U : SmoothDisjointUnionData pieces A)
    (V : SmoothDisjointUnionData pieces B) (x : A.carrier) : B.carrier :=
  (V.identify (unionRegionIndex U x)).map
    ((U.identify (unionRegionIndex U x)).inverse x)

theorem unionComparisonMap_of_mem (U : SmoothDisjointUnionData pieces A)
    (V : SmoothDisjointUnionData pieces B) {x : A.carrier} {i : Fin n}
    (hx : x ∈ U.region i) :
    unionComparisonMap U V x = (V.identify i).map ((U.identify i).inverse x) := by
  dsimp only [unionComparisonMap]
  rw [unionRegionIndex_eq U hx]

theorem unionComparisonMap_mem (U : SmoothDisjointUnionData pieces A)
    (V : SmoothDisjointUnionData pieces B) {x : A.carrier} {i : Fin n}
    (hx : x ∈ U.region i) : unionComparisonMap U V x ∈ V.region i := by
  rw [unionComparisonMap_of_mem U V hx]
  exact (V.identify i).map_image.subset (Set.mem_image_of_mem _ (Set.mem_univ _))

theorem unionComparisonMap_left_inverse (U : SmoothDisjointUnionData pieces A)
    (V : SmoothDisjointUnionData pieces B) :
    Function.LeftInverse (unionComparisonMap V U) (unionComparisonMap U V) := by
  intro x
  let i := unionRegionIndex U x
  have hx : x ∈ U.region i := unionRegionIndex_mem U x
  have hy : unionComparisonMap U V x ∈ V.region i := unionComparisonMap_mem U V hx
  rw [unionComparisonMap_of_mem V U hy, unionComparisonMap_of_mem U V hx,
    (V.identify i).left_inverse (Set.mem_univ _), (U.identify i).right_inverse hx]

theorem unionComparisonMap_smooth (U : SmoothDisjointUnionData pieces A)
    (V : SmoothDisjointUnionData pieces B) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (unionComparisonMap U V) := by
  intro x
  let i := unionRegionIndex U x
  have hx : x ∈ U.region i := unionRegionIndex_mem U x
  have hlocal : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun y => (V.identify i).map ((U.identify i).inverse y)) (U.region i) :=
    (V.identify i).map_smooth.comp (U.identify i).inverse_smooth
      (fun _ _ => Set.mem_univ _)
  have hmap : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (unionComparisonMap U V) (U.region i) :=
    hlocal.congr (fun _ hy => unionComparisonMap_of_mem U V hy)
  exact hmap.contMDiffAt ((U.region_open i).mem_nhds hx)

noncomputable def unionComparisonDiffeomorph
    (U : SmoothDisjointUnionData pieces A) (V : SmoothDisjointUnionData pieces B) :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞ where
  toEquiv := {
    toFun := unionComparisonMap U V
    invFun := unionComparisonMap V U
    left_inv := unionComparisonMap_left_inverse U V
    right_inv := unionComparisonMap_left_inverse V U }
  contMDiff_toFun := unionComparisonMap_smooth U V
  contMDiff_invFun := unionComparisonMap_smooth V U

end PoincareConjecture.M38
