import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Lifting controlled maps into open submanifolds

A chosen point totalizes a map into an open target. On any set mapped
into that target, the lift retains the map, its exact image, and its
smoothness. This is used for the punctured regions and collar in the
component restriction of Morgan--Tian Corollary 15.4(2), pp. 358-359.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

section Sets

variable {X Y : Type*} [TopologicalSpace Y] (U : Opens Y) (y0 : U) (f : X → Y)

/-- Lift a map into an open target, using a specified point where the map
leaves that target (MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def liftMap : X → U := by
  classical
  exact fun x => if h : f x ∈ U then ⟨f x, h⟩ else y0

/-- The lift preserves every value already in the target
(MT Corollary 15.4(2), pp. 358-359). -/
theorem liftMap_val_of_mem {x : X} (hx : f x ∈ U) :
    (U.liftMap y0 f x).val = f x := by
  simp only [liftMap, dif_pos hx]

/-- On a controlled set the lifted image is exactly the original image
inside the open subtype (MT Corollary 15.4(2), pp. 358-359). -/
theorem liftMap_image {s : Set X} (h : MapsTo f s U) :
    U.liftMap y0 f '' s = Subtype.val ⁻¹' (f '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (U.liftMap_val_of_mem y0 f (h hx)).symm⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Subtype.ext ((U.liftMap_val_of_mem y0 f (h hx)).trans hxy)⟩

end Sets

section Smoothness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (U : Opens N) (y0 : U) {f : M → N} {s : Set M} {n : ℕ∞ω}

/-- Smoothness on a controlled set is preserved by the open-target lift;
no regularity is claimed elsewhere (MT Corollary 15.4(2), pp. 358-359). -/
theorem contMDiffOn_liftMap (hf : ContMDiffOn I J n f s) (h : MapsTo f s U) :
    ContMDiffOn I J n (U.liftMap y0 f) s := by
  intro x hx
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (U.liftMap y0 f) s x).mp
  exact (hf x hx).congr
    (fun y hy => U.liftMap_val_of_mem y0 f (h hy))
    (U.liftMap_val_of_mem y0 f (h hx))

end Smoothness

end TopologicalSpace.Opens
