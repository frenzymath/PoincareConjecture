import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# A smooth defining function from the inverse collar

The transverse coordinate of the inverse of a smooth product chart
is a smooth function with nonvanishing derivative. Its level sets are
exactly the images of product slices. This supplies the defining
function in Hatcher's surface neighborhoods, Notes on Basic
3-Manifold Topology, Theorem 1.1 and Lemma 1.2, pp. 1-3.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M25.Topology3D

variable {M F : Type*} [TopologicalSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The total inverse transverse coordinate, used only on the chart
target; Hatcher's collar parameter, Theorem 1.1, pp. 1-2. -/
noncomputable def collarParameter (e : OpenPartialHomeomorph (M × ℝ) F) (y : F) : ℝ :=
  (e.symm y).2

omit [NormedSpace ℝ F] in
/-- On the chart source the inverse parameter recovers the given
transverse coordinate exactly. -/
theorem collarParameter_apply (e : OpenPartialHomeomorph (M × ℝ) F)
    (p : M × ℝ) (hp : p ∈ e.source) : collarParameter e (e p) = p.2 := by
  exact congrArg Prod.snd (e.left_inv hp)

omit [NormedSpace ℝ F] in
/-- Each level in the target is precisely the image of its product
slice in the source. No assertion is made outside the chart target. -/
theorem collarParameter_level (e : OpenPartialHomeomorph (M × ℝ) F) (a : ℝ) :
    {y ∈ e.target | collarParameter e y = a} =
      e '' (e.source ∩ (univ ×ˢ ({a} : Set ℝ))) := by
  ext y
  constructor
  · rintro ⟨hy, hya⟩
    exact ⟨e.symm y, ⟨e.map_target hy, mem_univ _, hya⟩, e.right_inv hy⟩
  · rintro ⟨p, ⟨hp, _, hpa⟩, rfl⟩
    exact ⟨e.map_source hp, (collarParameter_apply e p hp).trans hpa⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ChartedSpace E M]
variable (e : OpenPartialHomeomorph (M × ℝ) F)
variable (hi : ContMDiffOn 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)

include hi

/-- The inverse transverse coordinate is smooth on the chart target. -/
theorem collarParameter_contDiffOn : ContDiffOn ℝ ∞ (collarParameter e) e.target := by
  have h : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (collarParameter e) e.target :=
    fun y hy => (hi y hy).snd
  exact h.contDiffOn

/-- A smooth product chart has a transverse parameter with nonzero
ambient derivative, by the chain rule along its transverse lines. -/
theorem collarParameter_fderiv_ne_zero
    (he : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ e e.source)
    (p : M × ℝ) (hp : p ∈ e.source) :
    fderiv ℝ (collarParameter e) (e p) ≠ 0 := by
  have hpair : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (p.1, t)) := contMDiff_const.prodMk contMDiff_id
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => e (p.1, t)) p.2 :=
    ((he.contMDiffAt (e.open_source.mem_nhds hp)).comp p.2 hpair.contMDiffAt).contDiffAt
  have hr := ((collarParameter_contDiffOn e hi).contDiffAt
    (e.open_target.mem_nhds (e.map_source hp))).differentiableAt (by simp)
  intro hzero
  have hd := hr.hasFDerivAt.comp_hasDerivAt p.2 ((hc.differentiableAt (by simp)).hasDerivAt)
  rw [hzero, zero_apply] at hd
  have hid : HasDerivAt (fun t : ℝ => t) 0 p.2 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [hpair.continuous.continuousAt.eventually
      (e.open_source.mem_nhds hp)] with t ht
    exact (collarParameter_apply e (p.1, t) ht).symm
  have h01 := hid.unique (hasDerivAt_id p.2)
  exact zero_ne_one h01

end PoincareMT.M25.Topology3D
