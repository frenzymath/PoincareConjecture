import PoincareConjecture.Proofs.M74.Cor15_4.SchoenfliesRadialCoordinate
import PoincareConjecture.Proofs.M74.Mathlib.IncreasingRadiusChart
import Mathlib.Analysis.Calculus.Deriv.Inverse

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M74

private noncomputable def antitoneIntervalChart (f : ℝ → ℝ) (a b c d : ℝ)
    (hm : StrictAntiOn f (Ioo a b)) (himage : f '' Ioo a b = Ioo c d) :
    OpenPartialHomeomorph ℝ ℝ := by
  let F : Ioo a b → OrderDual (Ioo c d) := fun x =>
    ⟨f x.1, himage ▸ mem_image_of_mem f x.2⟩
  have hFm : StrictMono F := fun x y hxy => hm x.2 y.2 hxy
  have hFs : Function.Surjective F := by
    intro y
    obtain ⟨x, hx, hxy⟩ : y.1 ∈ f '' Ioo a b := by rw [himage]; exact y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := hFm.orderIsoOfSurjective F hFs
  have hb : BijOn f (Ioo a b) (Ioo c d) :=
    ⟨fun x hx => himage ▸ mem_image_of_mem _ hx, hm.injOn, by
      intro y hy
      rw [← himage] at hy
      exact hy⟩
  let p := hb.toPartialEquiv f (Ioo a b) (Ioo c d)
  have hc : ContinuousOn f (Ioo a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_subtype_val.comp e.continuous
  have ho : IsOpenMap ((Ioo a b).domRestrict f) :=
    isOpen_Ioo.isOpenMap_subtype_val.comp e.toHomeomorph.isOpenMap
  exact OpenPartialHomeomorph.ofContinuousOpenRestrict p hc ho isOpen_Ioo

end PoincareConjecture.M74

namespace PoincareConjecture.SurgeryBallEmbedding

open M74 M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)
  (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
  (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
  (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) (q : UnitTwoSphere)

private theorem inner_radius_interval :
    Icc (-1 / 16 : ℝ) (1 / 16) ⊆ Ioo (-1 / 8 : ℝ) (1 / 8) := by
  intro s hs
  constructor <;> linarith [hs.1, hs.2]

include Ψ hΨ hleft q in

theorem shiftedSchoenfliesRadius_image :
    B.shiftedSchoenfliesRadius d D '' Ioo (-1 / 16 : ℝ) (1 / 16) =
      Ioo (B.shiftedSchoenfliesRadius d D (1 / 16))
        (B.shiftedSchoenfliesRadius d D (-1 / 16)) := by
  have hc : ContinuousOn (B.shiftedSchoenfliesRadius d D) (Icc (-1 / 16 : ℝ) (1 / 16)) := by
    intro s hs
    exact (B.shiftedSchoenfliesRadius_contDiffAt d D Ψ hΨ hleft q
      (inner_radius_interval hs)).continuousAt.continuousWithinAt
  exact hc.image_Ioo_of_strictAntiOn (by norm_num)
    ((B.shiftedSchoenfliesRadius_strictAntiOn d D).mono inner_radius_interval)

noncomputable def shiftedSchoenfliesRadiusChart : OpenPartialHomeomorph ℝ ℝ :=
  antitoneIntervalChart (B.shiftedSchoenfliesRadius d D) (-1 / 16) (1 / 16)
    (B.shiftedSchoenfliesRadius d D (1 / 16)) (B.shiftedSchoenfliesRadius d D (-1 / 16))
    ((B.shiftedSchoenfliesRadius_strictAntiOn d D).mono
      (fun _ hs => inner_radius_interval ⟨hs.1.le, hs.2.le⟩))
    (B.shiftedSchoenfliesRadius_image d D Ψ hΨ hleft q)

@[simp] theorem shiftedSchoenfliesRadiusChart_source :
    (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).source =
      Ioo (-1 / 16 : ℝ) (1 / 16) := rfl

@[simp] theorem shiftedSchoenfliesRadiusChart_target :
    (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).target =
      Ioo (B.shiftedSchoenfliesRadius d D (1 / 16))
        (B.shiftedSchoenfliesRadius d D (-1 / 16)) := rfl

@[simp] theorem shiftedSchoenfliesRadiusChart_apply (s : ℝ) :
    B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q s =
      B.shiftedSchoenfliesRadius d D s := rfl

theorem shiftedSchoenfliesRadiusChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).symm
      (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).target := by
  let e := B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q
  intro r hr
  have hx : e.symm r ∈ Ioo (-1 / 8 : ℝ) (1 / 8) := by
    have hs : e.symm r ∈ Ioo (-1 / 16 : ℝ) (1 / 16) := e.map_target hr
    exact inner_radius_interval ⟨hs.1.le, hs.2.le⟩
  have hf := B.shiftedSchoenfliesRadius_contDiffAt d D Ψ hΨ hleft q hx
  exact (e.contDiffAt_symm_deriv
    (B.shiftedSchoenfliesRadius_deriv_neg d D Ψ hΨ hleft q hx).ne hr
    (hf.differentiableAt (by simp)).hasDerivAt hf).contDiffWithinAt

theorem shiftedSchoenfliesRadiusChart_symm_deriv_neg {r : ℝ}
    (hr : r ∈ (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).target) :
    deriv (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).symm r < 0 := by
  let e := B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q
  have hx : e.symm r ∈ Ioo (-1 / 8 : ℝ) (1 / 8) := by
    have hs : e.symm r ∈ Ioo (-1 / 16 : ℝ) (1 / 16) := e.map_target hr
    exact inner_radius_interval ⟨hs.1.le, hs.2.le⟩
  have hf := B.shiftedSchoenfliesRadius_contDiffAt d D Ψ hΨ hleft q hx
  have hd := B.shiftedSchoenfliesRadius_deriv_neg d D Ψ hΨ hleft q hx
  have hi := e.hasDerivAt_symm hr hd.ne (hf.differentiableAt (by simp)).hasDerivAt
  rw [hi.deriv]
  exact inv_lt_zero.mpr hd

theorem shiftedSchoenfliesRadiusChart_symm_boundary :
    (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).symm (D.radial (1 / 2)) = 0 := by
  have h := (B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q).left_inv
    (show (0 : ℝ) ∈ Ioo (-1 / 16 : ℝ) (1 / 16) by norm_num)
  simpa only [B.shiftedSchoenfliesRadiusChart_apply d D Ψ hΨ hleft q,
    B.shiftedSchoenfliesRadius_zero d D] using h

end PoincareConjecture.SurgeryBallEmbedding
