import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.OpenPartialHomeomorph.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem exists_diffeomorph_of_local_radial_flow
    (Φ : ℝ → M → M)
    (hΦ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞ (Function.uncurry Φ))
    (hzero : ∀ x, Φ 0 x = x)
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (e : OpenPartialHomeomorph E M)
    (he : ContMDiffOn 𝓘(ℝ, E) I ∞ e e.source)
    (heinv : ContMDiffOn I 𝓘(ℝ, E) ∞ e.symm e.target)
    {r : ℝ} (hr : 0 < r) (hsource : ball (0 : E) r ⊆ e.source)
    (hlocal : ∀ t ≤ 0, ∀ v ∈ ball (0 : E) r,
      Φ t (e v) = e (Real.exp t • v))
    (hhit : ∀ x : M, ∃ t : ℝ, Φ t x ∈ e '' ball (0 : E) r) :
    ∃ d : Diffeomorph 𝓘(ℝ, E) I E M ∞,
      ∀ v ∈ ball (0 : E) r, d v = e v := by
  classical
  have hslice (t : ℝ) : ContMDiff I I ∞ (Φ t) :=
    hΦ.comp (contMDiff_const.prodMk contMDiff_id)
  have hcancel (t : ℝ) (x : M) : Φ (-t) (Φ t x) = x := by
    rw [← hadd, neg_add_cancel, hzero]
  have hcancel' (t : ℝ) (x : M) : Φ t (Φ (-t) x) = x := by
    rw [← hadd, add_neg_cancel, hzero]
  have hscale_cancel (t : ℝ) (v : E) :
      Real.exp (-t) • (Real.exp t • v) = v := by
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  have hscale_cancel' (t : ℝ) (v : E) :
      Real.exp t • (Real.exp (-t) • v) = v := by
    rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  have hfull (t : ℝ) (v : E) (hv : v ∈ ball (0 : E) r)
      (htv : Real.exp t • v ∈ ball (0 : E) r) :
      Φ t (e v) = e (Real.exp t • v) := by
    by_cases ht : t ≤ 0
    · exact hlocal t ht v hv
    · have hh := hlocal (-t) (by linarith) (Real.exp t • v) htv
      rw [hscale_cancel] at hh
      rw [← hh, hcancel']
  have hsmall_eventually (v : E) :
      ∀ᶠ t : ℝ in atBot, Real.exp t • v ∈ ball (0 : E) r := by
    have htend : Tendsto (fun t : ℝ => Real.exp t • v) atBot (𝓝 (0 : E)) := by
      simpa only [zero_smul] using Real.tendsto_exp_atBot.smul_const v
    exact htend.eventually (ball_mem_nhds _ hr)
  have hsmall (v : E) : ∃ t : ℝ, Real.exp t • v ∈ ball (0 : E) r :=
    (hsmall_eventually v).exists
  have hcompat (v : E) (s t : ℝ)
      (hs : Real.exp s • v ∈ ball (0 : E) r)
      (ht : Real.exp t • v ∈ ball (0 : E) r) :
      Φ (-s) (e (Real.exp s • v)) = Φ (-t) (e (Real.exp t • v)) := by
    have hst : Real.exp (t - s) • (Real.exp s • v) = Real.exp t • v := by
      rw [smul_smul, ← Real.exp_add, sub_add_cancel]
    have hh := hfull (t - s) (Real.exp s • v) hs (hst.symm ▸ ht)
    rw [hst] at hh
    rw [← hh, ← hadd]
    congr 1
    ring
  let F : E → M := fun v =>
    Φ (-(hsmall v).choose) (e (Real.exp (hsmall v).choose • v))
  have hFeq (v : E) (t : ℝ) (ht : Real.exp t • v ∈ ball (0 : E) r) :
      F v = Φ (-t) (e (Real.exp t • v)) :=
    hcompat v _ t (hsmall v).choose_spec ht
  have hFball (v : E) (hv : v ∈ ball (0 : E) r) : F v = e v := by
    simpa only [neg_zero, Real.exp_zero, one_smul, hzero] using
      hFeq v 0 (by simpa only [Real.exp_zero, one_smul] using hv)
  have hFinj : Function.Injective F := by
    intro v w hvw
    obtain ⟨t, htv, htw⟩ := ((hsmall_eventually v).and (hsmall_eventually w)).exists
    rw [hFeq v t htv, hFeq w t htw] at hvw
    have hh := congrArg (Φ t) hvw
    rw [hcancel', hcancel'] at hh
    have hs := e.injOn (hsource htv) (hsource htw) hh
    have hh' := congrArg (fun z : E => Real.exp (-t) • z) hs
    simpa only [hscale_cancel] using hh'
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨t, v, hv, heq⟩ := hhit x
    refine ⟨Real.exp (-t) • v, ?_⟩
    rw [hFeq _ t (by simpa only [hscale_cancel'] using hv), hscale_cancel', heq,
      hcancel]
  let d : E ≃ M := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  have hd (v : E) : d v = F v := rfl
  have hFsm : ContMDiff 𝓘(ℝ, E) I ∞ F := by
    intro v
    obtain ⟨t, ht⟩ := hsmall v
    have hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => Real.exp t • w) :=
      (contDiff_id.const_smul (Real.exp t)).contMDiff
    have he' := he.contMDiffAt (e.open_source.mem_nhds (hsource ht))
    have hsm := (hslice (-t)).contMDiffAt.comp v (he'.comp v hs.contMDiffAt)
    apply hsm.congr_of_eventuallyEq
    have hnear := hs.continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds ht)
    filter_upwards [hnear] with w hw
    exact hFeq w t hw
  have himage : IsOpen (e '' ball (0 : E) r) :=
    e.isOpen_image_of_subset_source isOpen_ball hsource
  have hinveq (x : M) (t : ℝ) (hx : Φ t x ∈ e '' ball (0 : E) r) :
      d.symm x = Real.exp (-t) • e.symm (Φ t x) := by
    obtain ⟨v, hv, heq⟩ := hx
    apply d.injective
    rw [d.apply_symm_apply, hd, ← heq, e.left_inv (hsource hv)]
    rw [hFeq _ t (by simpa only [hscale_cancel'] using hv), hscale_cancel', heq,
      hcancel]
  have hinvsm : ContMDiff I 𝓘(ℝ, E) ∞ d.symm := by
    intro x
    obtain ⟨t, ht⟩ := hhit x
    have htarget : Φ t x ∈ e.target := by
      obtain ⟨v, hv, heq⟩ := ht
      exact heq ▸ e.map_source (hsource hv)
    have he' := heinv.contMDiffAt (e.open_target.mem_nhds htarget)
    have hsm : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun y : M => Real.exp (-t) • e.symm (Φ t y)) x :=
      (contDiff_id.const_smul (Real.exp (-t))).contMDiff.contMDiffAt.comp x
        (he'.comp x (hslice t).contMDiffAt)
    apply hsm.congr_of_eventuallyEq
    have hnear := (hslice t).continuous.continuousAt.preimage_mem_nhds
      (himage.mem_nhds ht)
    filter_upwards [hnear] with y hy
    exact hinveq y t hy
  exact ⟨⟨d, hFsm, hinvsm⟩, hFball⟩

end Poincare.Manifold
