import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Coordinates.ExponentialSlice
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The global diffeomorphism of an everywhere regular exponential slice

The total forward and inverse maps are the frozen exponential chart maps.
When both canonical domains are the whole spaces, their existing smoothness
and inverse laws give a global diffeomorphism without any new choice.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

/-- A full canonical regular slice is the actual global smooth exponential equivalence. -/
noncomputable def exponentialSliceDiffeomorph (G : LExponentialGeometry F T τmax p) (τ : ℝ)
    (hsource : (exponentialSliceChart G τ).source = univ)
    (htarget : (exponentialSliceChart G τ).target = univ) :
    Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞ where
  toEquiv :=
    { toFun := exponentialSliceChart G τ
      invFun := (exponentialSliceChart G τ).symm
      left_inv := fun x ↦ (exponentialSliceChart G τ).left_inv (hsource.symm ▸ mem_univ x)
      right_inv := fun q ↦ (exponentialSliceChart G τ).right_inv (htarget.symm ▸ mem_univ q) }
  contMDiff_toFun := by
    apply contMDiffOn_univ.mp
    have h := exponentialSliceChart_contMDiffOn G τ
    rwa [hsource] at h
  contMDiff_invFun := by
    apply contMDiffOn_univ.mp
    have h := exponentialSliceChart_symm_contMDiffOn G τ
    rwa [htarget] at h

end PoincareMT.ReducedVolume
