import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1



theorem mfderiv_eq_zero_iff_fderiv_sphere_coordinates_eq_zero
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {x : E2} (hx : x ∈ e.source) :
    mfderiv (𝓡 2) 𝓘(Real, Real) h (e x) = 0 ↔
      fderiv Real (h ∘ e) x = 0 := by
  let d : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }
  have heloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e x :=
    ⟨d, hx, fun _ _ => rfl⟩
  have hesurj : Function.Surjective (mfderiv (𝓡 2) (𝓡 2) e x) :=
    (heloc.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hchain := mfderiv_comp x ((hh (e x)).mdifferentiableAt (by simp))
    (heloc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  constructor
  · intro hzero
    rw [hchain, hzero]
    rfl
  · intro hzero
    ext u
    obtain ⟨w, rfl⟩ := hesurj u
    exact congrArg (fun L : E2 →L[Real] Real => L w) (hchain.symm.trans hzero)



theorem mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eventuallyEq
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {x : E2} (hx : x ∈ e.source) {g : E2 -> Real}
    (hg : h ∘ e =ᶠ[𝓝 x] g) :
    mfderiv (𝓡 2) 𝓘(Real, Real) h (e x) = 0 ↔ fderiv Real g x = 0 := by
  rw [mfderiv_eq_zero_iff_fderiv_sphere_coordinates_eq_zero hh e he hei hx,
    hg.fderiv_eq]



theorem mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {x : E2} (hx : x ∈ e.source) {g : E2 -> Real}
    (hg : EqOn (h ∘ e) g e.source) :
    mfderiv (𝓡 2) 𝓘(Real, Real) h (e x) = 0 ↔ fderiv Real g x = 0 :=
  mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eventuallyEq hh e he hei hx
    (eventuallyEq_of_mem (e.open_source.mem_nhds hx) hg)

end Poincare.Manifold.Schoenflies
