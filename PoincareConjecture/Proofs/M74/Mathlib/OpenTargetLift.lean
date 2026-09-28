import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

section Sets

variable {X Y : Type*} [TopologicalSpace Y] (U : Opens Y) (y0 : U) (f : X → Y)

noncomputable def liftMap : X → U := by
  classical
  exact fun x => if h : f x ∈ U then ⟨f x, h⟩ else y0

theorem liftMap_val_of_mem {x : X} (hx : f x ∈ U) :
    (U.liftMap y0 f x).val = f x := by
  simp only [liftMap, dif_pos hx]

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
