import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# One chart replacement in manifold approximation

A smooth cutoff replaces coordinates on its plateau and leaves the original
map unchanged off its support. Chart membership is an explicit hypothesis;
smoothness already obtained by earlier replacements is preserved. This is
the finite-chart approximation step used for MT Claim 18.16, printed p. 430.
-/

set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Topology

noncomputable section

namespace PoincareMT.Proofs.M59

variable {E H X F K M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  (J : ModelWithCorners ℝ F K)
  [TopologicalSpace M] [ChartedSpace K M]

/-- Replace the coordinate map where the cutoff is nonzero.
Source: the finite-chart approximation derivation for MT Claim 18.16, p. 430. -/
def chartPatch (c : M) (b : X → ℝ) (v : X → F) (f : X → M) (x : X) : M :=
  if b x = 0 then f x else
    (extChartAt J c).symm ((1 - b x) • extChartAt J c (f x) + b x • v x)

omit [TopologicalSpace X] in
/-- A zero cutoff leaves the complete value unchanged.
Source: MT Claim 18.16, p. 430, chart approximation derivation. -/
theorem chartPatch_of_weight_zero (c : M) (b : X → ℝ) (v : X → F) (f : X → M)
    {x : X} (hx : b x = 0) : chartPatch J c b v f x = f x := by
  simp only [chartPatch, hx, if_true]

/-- Off the closed support, replacement agrees locally with the original map.
Source: MT Claim 18.16, p. 430, chart approximation derivation. -/
theorem chartPatch_eventually_of_not_mem_tsupport
    (c : M) (b : X → ℝ) (v : X → F) (f : X → M) {x : X} (hx : x ∉ tsupport b) :
    chartPatch J c b v f =ᶠ[𝓝 x] f := by
  filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hx] with y hy
  apply chartPatch_of_weight_zero
  exact notMem_support.mp (fun h => hy (subset_closure h))

/-- Near a point mapped into the chart source, both branches have the
same coordinate formula. Source: MT Claim 18.16, p. 430, chart approximation. -/
theorem chartPatch_eventually_formula
    (c : M) (b : X → ℝ) (v : X → F) (f : X → M) {x : X}
    (hf : ContinuousAt f x) (hx : f x ∈ (extChartAt J c).source) :
    chartPatch J c b v f =ᶠ[𝓝 x]
      (fun y => (extChartAt J c).symm ((1 - b y) • extChartAt J c (f y) + b y • v y)) := by
  filter_upwards [hf ((isOpen_extChartAt_source c).mem_nhds hx)] with y hy
  unfold chartPatch
  split_ifs with hb
  · simpa only [hb, sub_zero, one_smul, zero_smul, add_zero] using
      ((extChartAt J c).left_inv hy).symm
  · rfl

variable [J.Boundaryless] [IsManifold J ∞ M]

/-- The replacement is continuous if its supported coordinate segments stay
inside the chart. Source: MT Claim 18.16, p. 430, chart approximation. -/
theorem continuous_chartPatch (c : M) (b : X → ℝ) (v : X → F) (f : X → M)
    (hb : Continuous b) (hv : Continuous v) (hf : Continuous f)
    (hsource : ∀ x ∈ tsupport b, f x ∈ (extChartAt J c).source)
    (htarget : ∀ x ∈ tsupport b,
      (1 - b x) • extChartAt J c (f x) + b x • v x ∈ (extChartAt J c).target) :
    Continuous (chartPatch J c b v f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport b
  · have hc : ContinuousAt (fun y => extChartAt J c (f y)) x :=
      ((contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsource x hx) :
        ContMDiffAt J 𝓘(ℝ, F) ∞ (extChartAt J c) (f x)).continuousAt).comp hf.continuousAt
    have hi : ContinuousAt (fun y => (1 - b y) • extChartAt J c (f y) + b y • v y) x :=
      ((continuousAt_const.sub hb.continuousAt).smul hc).add (hb.continuousAt.smul hv.continuousAt)
    have hmain : ContinuousAt (fun y => (extChartAt J c).symm
        ((1 - b y) • extChartAt J c (f y) + b y • v y)) x :=
      (((contMDiffOn_extChartAt_symm c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds (htarget x hx)) :
        ContMDiffAt 𝓘(ℝ, F) J ∞ (extChartAt J c).symm _).continuousAt).comp
          (f := fun y => (1 - b y) • extChartAt J c (f y) + b y • v y) hi
    exact hmain.congr_of_eventuallyEq
      (chartPatch_eventually_formula J c b v f hf.continuousAt (hsource x hx))
  · exact hf.continuousAt.congr_of_eventuallyEq
      (chartPatch_eventually_of_not_mem_tsupport J c b v f hx)

/-- A chart replacement preserves every point where the map is already smooth.
Source: the finite-chart induction for MT Claim 18.16, p. 430. -/
theorem contMDiffAt_chartPatch_of_contMDiffAt
    (c : M) (b : X → ℝ) (v : X → F) (f : X → M)
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b) (hv : ContMDiff I 𝓘(ℝ, F) ∞ v)
    (hsource : ∀ x ∈ tsupport b, f x ∈ (extChartAt J c).source)
    (htarget : ∀ x ∈ tsupport b,
      (1 - b x) • extChartAt J c (f x) + b x • v x ∈ (extChartAt J c).target)
    {x : X} (hf : ContMDiffAt I J ∞ f x) :
    ContMDiffAt I J ∞ (chartPatch J c b v f) x := by
  by_cases hx : x ∈ tsupport b
  · have hc : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => extChartAt J c (f y)) x :=
      (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsource x hx)).comp x hf
    have hi : ContMDiffAt I 𝓘(ℝ, F) ∞
        (fun y => (1 - b y) • extChartAt J c (f y) + b y • v y) x :=
      ((contMDiffAt_const.sub hb.contMDiffAt).smul hc).add (hb.contMDiffAt.smul hv.contMDiffAt)
    apply (((contMDiffOn_extChartAt_symm c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds (htarget x hx))).comp x hi).congr_of_eventuallyEq
    exact chartPatch_eventually_formula J c b v f hf.continuousAt (hsource x hx)
  · exact hf.congr_of_eventuallyEq (chartPatch_eventually_of_not_mem_tsupport J c b v f hx)

/-- On a plateau the new coordinate map supplies smoothness even if the
original map is only continuous. Source: MT Claim 18.16, p. 430, chart approximation. -/
theorem contMDiffAt_chartPatch_of_plateau
    (c : M) (b : X → ℝ) (v : X → F) (f : X → M)
    (hv : ContMDiff I 𝓘(ℝ, F) ∞ v) (hf : Continuous f)
    (hsource : ∀ x ∈ tsupport b, f x ∈ (extChartAt J c).source)
    (htarget : ∀ x ∈ tsupport b,
      (1 - b x) • extChartAt J c (f x) + b x • v x ∈ (extChartAt J c).target)
    {x : X} (hb : b =ᶠ[𝓝 x] 1) : ContMDiffAt I J ∞ (chartPatch J c b v f) x := by
  have hx : x ∈ tsupport b := subset_closure (by
    change b x ≠ 0
    rw [hb.eq_of_nhds]
    exact one_ne_zero)
  have htx : v x ∈ (extChartAt J c).target := by
    simpa only [hb.eq_of_nhds, Pi.one_apply, sub_self, zero_smul, one_smul, zero_add]
      using htarget x hx
  apply (((contMDiffOn_extChartAt_symm c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds htx)).comp x hv.contMDiffAt).congr_of_eventuallyEq
  filter_upwards [chartPatch_eventually_formula J c b v f hf.continuousAt (hsource x hx), hb]
    with y hy hby
  simpa only [hby, Pi.one_apply, sub_self, zero_smul, one_smul, zero_add,
    Function.comp_apply] using hy

omit [J.Boundaryless] [IsManifold J ∞ M] in
/-- Matching a fixed coordinate value preserves that value exactly.
Source: the constant-boundary clause for MT Claim 18.16, p. 430. -/
theorem chartPatch_preserves_value
    (c : M) (b : X → ℝ) (v : X → F) (f : X → M)
    (hsource : ∀ x ∈ tsupport b, f x ∈ (extChartAt J c).source)
    (p : M) (hp : ∀ x ∈ tsupport b, f x = p → v x = extChartAt J c p)
    {x : X} (hx : f x = p) : chartPatch J c b v f x = p := by
  by_cases hb : b x = 0
  · exact (chartPatch_of_weight_zero J c b v f hb).trans hx
  · have hxs : x ∈ tsupport b := subset_closure hb
    simp only [chartPatch, hb, if_false, hp x hxs hx, ← hx, ← add_smul, sub_add_cancel, one_smul]
    exact (extChartAt J c).left_inv (hsource x hxs)

end PoincareMT.Proofs.M59
