import PoincareLib.Topology.Manifold.Surgery.Reduction.Algebra.PositiveRadiusSplice
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Smooth charts from strictly increasing scalar radii

An exact interval image and strict increase give an order isomorphism,
and hence an actual open partial homeomorphism. Nonzero derivative gives
the smooth inverse needed by the radial construction in MT Corollary
15.4(2), pp. 358-359.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff Topology

namespace PoincareMT.M74

/-- Package a strictly increasing radius with its exact positive image
as an actual interval chart (MT Corollary 15.4(2), pp. 358-359). -/
noncomputable def increasingRadiusChart (f : ℝ → ℝ) (R : ℝ)
    (hm : StrictMonoOn f (Ioo 0 R)) (himage : f '' Ioo 0 R = Ioi 0) :
    OpenPartialHomeomorph ℝ ℝ := by
  let F : Ioo (0 : ℝ) R → Ioi (0 : ℝ) := fun x =>
    ⟨f x.1, himage ▸ mem_image_of_mem f x.2⟩
  have hFm : StrictMono F := fun x y hxy => hm x.2 y.2 hxy
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x, hx, hxy⟩ : y.1 ∈ f '' Ioo 0 R := by rw [himage]; exact y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := hFm.orderIsoOfSurjective F hFs
  have hb : BijOn f (Ioo 0 R) (Ioi 0) :=
    ⟨fun x hx => himage ▸ mem_image_of_mem _ hx, hm.injOn, by
      intro y hy
      rw [← himage] at hy
      exact hy⟩
  let p := hb.toPartialEquiv f (Ioo 0 R) (Ioi 0)
  have hc : ContinuousOn f (Ioo 0 R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp e.continuous
  have ho : IsOpenMap ((Ioo (0 : ℝ) R).domRestrict f) :=
    isOpen_Ioi.isOpenMap_subtype_val.comp e.toHomeomorph.isOpenMap
  exact OpenPartialHomeomorph.ofContinuousOpenRestrict p hc ho isOpen_Ioo

/-- The increasing radius chart has the prescribed source interval
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem increasingRadiusChart_source (f : ℝ → ℝ) (R : ℝ)
    (hm : StrictMonoOn f (Ioo 0 R)) (himage : f '' Ioo 0 R = Ioi 0) :
    (increasingRadiusChart f R hm himage).source = Ioo 0 R := rfl

/-- The increasing radius chart covers exactly the positive radii
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem increasingRadiusChart_target (f : ℝ → ℝ) (R : ℝ)
    (hm : StrictMonoOn f (Ioo 0 R)) (himage : f '' Ioo 0 R = Ioi 0) :
    (increasingRadiusChart f R hm himage).target = Ioi 0 := rfl

/-- Packaging the radius leaves its forward map unchanged
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem increasingRadiusChart_apply (f : ℝ → ℝ) (R : ℝ)
    (hm : StrictMonoOn f (Ioo 0 R)) (himage : f '' Ioo 0 R = Ioi 0) (x : ℝ) :
    increasingRadiusChart f R hm himage x = f x := rfl

/-- A positive derivative makes the inverse radius smooth on its exact
target (MT Corollary 15.4(2), pp. 358-359). -/
theorem increasingRadiusChart_symm_contDiffOn (f : ℝ → ℝ) (R : ℝ)
    (hm : StrictMonoOn f (Ioo 0 R)) (himage : f '' Ioo 0 R = Ioi 0)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 R))
    (hfd : ∀ x ∈ Ioo 0 R, deriv f x ≠ 0) :
    ContDiffOn ℝ ∞ (increasingRadiusChart f R hm himage).symm (Ioi 0) := by
  let e := increasingRadiusChart f R hm himage
  intro y hy
  have hyt : y ∈ e.target := hy
  have hx : e.symm y ∈ Ioo (0 : ℝ) R := e.map_target hyt
  have hfx : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (isOpen_Ioo.mem_nhds hx)
  exact (e.contDiffAt_symm_deriv (hfd _ hx) hyt
    (hfx.differentiableAt (by simp)).hasDerivAt hfx).contDiffWithinAt

end PoincareMT.M74
