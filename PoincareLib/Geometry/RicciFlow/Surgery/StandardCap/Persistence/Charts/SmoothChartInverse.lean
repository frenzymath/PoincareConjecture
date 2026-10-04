import PoincareLib.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth inverse charts on open injectivity domains

An injective smooth map with nonsingular differential on an open set
has a smooth inverse on its image. The inverse is selected only on that
image. This is the chart step of Morgan--Tian, Claim 16.6 and
Corollary 16.7, pp. 371-372; see derivation 20.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

variable {n : ℕ} {M N : Type*} [Nonempty M] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]

omit [Nonempty M] in
/-- The image of an open nonsingularity domain is open, without an
injectivity assumption. -/
theorem isOpen_image_of_mfderiv_bijective {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hD : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsOpen (f '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (hf.contMDiffAt (hU.mem_nhds hx)) (hD x hx)]
  exact image_mem_map (hU.mem_nhds hx)

/-- The inverse chosen on an injectivity domain is smooth at all image
points when the original differential is nonsingular. -/
theorem contMDiffOn_invFunOn_of_mfderiv_bijective {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U) (hinj : InjOn f U)
    (hD : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Function.invFunOn f U) (f '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_of_local_left_inverse (hf.contMDiffAt (hU.mem_nhds hx)) (hD x hx)
  filter_upwards [hU.mem_nhds hx] with z hz
  exact hinj.leftInvOn_invFunOn hz

/-- The actual smooth map, restricted to its open injectivity domain,
defines a partial diffeomorphism onto its literal image. -/
noncomputable def partialDiffeomorphOfInjOn
    (f : M → N) (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U) (hinj : InjOn f U)
    (hD : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) M N ∞ where
  toFun := f
  invFun := Function.invFunOn f U
  source := U
  target := f '' U
  map_source' := fun _ hx => mem_image_of_mem f hx
  map_target' := fun _ hx => Function.invFunOn_mem hx
  left_inv' := hinj.leftInvOn_invFunOn
  right_inv' := fun _ hx => Function.invFunOn_eq hx
  open_source := hU
  open_target := isOpen_image_of_mfderiv_bijective hU hf hD
  contMDiffOn_toFun := hf
  contMDiffOn_invFun := contMDiffOn_invFunOn_of_mfderiv_bijective hU hf hinj hD

end Poincare
