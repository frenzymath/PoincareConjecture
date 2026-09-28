import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup



set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X]



structure OpenFrontierCollapse (R : Set X) where
  overlap : Set X
  positive : Set X
  negative : Set X
  overlap_open : IsOpen overlap
  positive_open : IsOpen positive
  negative_open : IsOpen negative
  positive_eq : positive = R ∪ overlap
  negative_eq : negative = (interior R)ᶜ ∪ overlap
  inter_eq : positive ∩ negative = overlap
  cover : positive ∪ negative = univ
  frontier_subset : frontier R ⊆ overlap
  motion : C(unitInterval × X, X)
  motion_zero : ∀ x, motion (0, x) = x
  motion_overlap : ∀ t, MapsTo (fun x => motion (t, x)) overlap overlap
  motion_positive : ∀ t, MapsTo (fun x => motion (t, x)) R R
  motion_negative : ∀ t, MapsTo (fun x => motion (t, x)) (interior R)ᶜ (interior R)ᶜ
  endpoint_overlap : MapsTo (fun x => motion (1, x)) overlap (frontier R)

namespace OpenFrontierCollapse

variable {R : Set X} (C : OpenFrontierCollapse R)

theorem positive_subset : R ⊆ C.positive := by rw [C.positive_eq]; exact subset_union_left

theorem negative_subset : (interior R)ᶜ ⊆ C.negative := by
  rw [C.negative_eq]; exact subset_union_left

theorem overlap_subset_positive : C.overlap ⊆ C.positive := by
  rw [C.positive_eq]; exact subset_union_right

theorem overlap_subset_negative : C.overlap ⊆ C.negative := by
  rw [C.negative_eq]; exact subset_union_right

end OpenFrontierCollapse

end PoincareConjecture.M76
