import PoincareConjecture.Proofs.M03.Existence.ConjugatorLieDerivativeNative
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real









set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped ContDiff Topology

namespace PoincareConjecture.ConjugatorLieDerivativeNative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mem_closure_interior_Ico_prod {U : Set E} (hU : IsOpen U)
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Ico 0 T) {x : E} (hx : x ∈ U) :
    (t, x) ∈ closure (interior (Set.Ico 0 T ×ˢ U)) := by
  rw [interior_prod_eq, interior_Ico, hU.interior_eq, closure_prod_eq,
    closure_Ioo (ne_of_lt hT)]
  exact ⟨⟨ht.1, ht.2.le⟩, subset_closure hx⟩

private theorem spatial_fderiv_eq_within {f : ℝ × E → F}
    {J : Set ℝ} {U : Set E} {t : ℝ} {x : E}
    (hU : IsOpen U) (ht : t ∈ J) (hx : x ∈ U)
    (hf : DifferentiableWithinAt ℝ f (J ×ˢ U) (t, x)) :
    fderiv ℝ (fun z => f (t, z)) x =
      (fderivWithin ℝ f (J ×ˢ U) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hmaps : ∀ᶠ z in 𝓝 x, (t, z) ∈ J ×ˢ U := by
    filter_upwards [hU.mem_nhds hx] with z hz using ⟨ht, hz⟩
  exact (hf.hasFDerivWithinAt.comp_hasFDerivAt x
    (hasFDerivAt_prodMk_right t x) hmaps).fderiv

theorem hasDerivWithinAt_spatial_fderiv_of_orbit
    {f : ℝ × E → F} {V : F → F} {J : Set ℝ} {U : Set E} {t : ℝ} {x : E}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (ht : t ∈ J) (hx : x ∈ U)
    (hinterior : (t, x) ∈ closure (interior (J ×ˢ U)))
    (hf : ContDiffWithinAt ℝ 2 f (J ×ˢ U) (t, x))
    (hV : DifferentiableAt ℝ V (f (t, x)))
    (horbit : ∀ᶠ z in 𝓝 x,
      HasDerivWithinAt (fun s => f (s, z)) (V (f (t, z))) J t)
    (u : E) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun z => f (s, z)) x u)
      (fderiv ℝ V (f (t, x)) (fderiv ℝ (fun z => f (t, z)) x u)) J t := by
  let S := J ×ˢ U
  have hS : UniqueDiffOn ℝ S := hJ.prod hU.uniqueDiffOn
  have hmem : (t, x) ∈ S := ⟨ht, hx⟩
  have hfd : DifferentiableWithinAt ℝ (fderivWithin ℝ f S) S (t, x) :=
    (hf.fderivWithin_right hS (m := 1) (by norm_num) hmem).differentiableWithinAt one_ne_zero
  have hlocal : ∀ᶠ q in 𝓝[S] (t, x), DifferentiableWithinAt ℝ f S q := by
    have h := hf.eventually (by norm_num)
    rw [Set.insert_eq_of_mem hmem] at h
    exact h.mono fun _ hq => hq.differentiableWithinAt two_ne_zero
  have hmapsTime : Set.MapsTo (fun s : ℝ => (s, x)) J S := fun _ hs => ⟨hs, hx⟩
  have htx : Filter.Tendsto (fun s : ℝ => (s, x)) (𝓝[J] t) (𝓝[S] (t, x)) :=
    (show ContinuousWithinAt (fun s : ℝ => (s, x)) J t from by fun_prop).tendsto_nhdsWithin hmapsTime
  have hspaceMem : ∀ᶠ z in 𝓝 x, (t, z) ∈ S := by
    filter_upwards [hU.mem_nhds hx] with z hz using ⟨ht, hz⟩
  have htz : Filter.Tendsto (fun z : E => (t, z)) (𝓝 x) (𝓝[S] (t, x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(continuous_const.prodMk continuous_id).continuousAt, hspaceMem⟩
  have htime : (fun z => fderivWithin ℝ f S (t, z) (1, 0)) =ᶠ[𝓝 x]
      (fun z => V (f (t, z))) := by
    filter_upwards [htz hlocal, horbit, hU.mem_nhds hx] with z hz hode hzU
    have hline : HasDerivWithinAt (fun s : ℝ => (s, z)) (1, 0) J t := by
      simpa using HasDerivWithinAt.prodMk (hasDerivWithinAt_id t J)
        (hasDerivWithinAt_const t J z)
    have hcurve := HasFDerivWithinAt.comp_hasDerivWithinAt t
      (f := fun s : ℝ => (s, z)) hz.hasFDerivWithinAt hline
      (fun _ hs => ⟨hs, hzU⟩)
    exact (hJ t ht).eq_deriv _ hcurve hode
  have hline : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) J t := by
    simpa using HasDerivWithinAt.prodMk (hasDerivWithinAt_id t J)
      (hasDerivWithinAt_const t J x)
  have hDtime := (HasFDerivWithinAt.comp_hasDerivWithinAt t
    (f := fun s : ℝ => (s, x)) hfd.hasFDerivWithinAt hline hmapsTime).clm_apply
      (hasDerivWithinAt_const t J ((0, u) : ℝ × E))
  have hspatial :
      (fun s => fderiv ℝ (fun z => f (s, z)) x u) =ᶠ[𝓝[J] t]
        (fun s => fderivWithin ℝ f S (s, x) (0, u)) := by
    filter_upwards [htx hlocal, self_mem_nhdsWithin] with s hs hsJ
    rw [spatial_fderiv_eq_within hU hsJ hx hs]
    rfl
  have hspush : HasDerivWithinAt (fun s => fderiv ℝ (fun z => f (s, z)) x u)
      (fderivWithin ℝ (fderivWithin ℝ f S) S (t, x) (1, 0) (0, u)) J t := by
    have hval : fderiv ℝ (fun z => f (t, z)) x u =
        fderivWithin ℝ f S (t, x) (0, u) := by
      rw [spatial_fderiv_eq_within hU ht hx (hf.differentiableWithinAt two_ne_zero)]
      rfl
    apply HasDerivWithinAt.congr_of_eventuallyEq _ hspatial hval
    simpa only [map_zero, add_zero, Function.comp_apply] using hDtime
  have hspaceTime : HasFDerivAt (fun z => fderivWithin ℝ f S (t, z) (1, 0))
      (((fderivWithin ℝ (fderivWithin ℝ f S) S (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)).flip (1, 0)) x := by
    have h := (hfd.hasFDerivWithinAt.comp_hasFDerivAt x
      (hasFDerivAt_prodMk_right t x) hspaceMem).clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × E) x)
    simpa using h
  have hslice : DifferentiableAt ℝ (fun z => f (t, z)) x :=
    ((hf.differentiableWithinAt two_ne_zero).hasFDerivWithinAt.comp_hasFDerivAt x
      (hasFDerivAt_prodMk_right t x) hspaceMem).differentiableAt
  have hcomp : HasFDerivAt (fun z => V (f (t, z)))
      ((fderiv ℝ V (f (t, x))).comp (fderiv ℝ (fun z => f (t, z)) x)) x :=
    hV.hasFDerivAt.comp x hslice.hasFDerivAt
  have hderivs := (hspaceTime.congr_of_eventuallyEq htime.symm).unique hcomp
  have hmixed := hf.isSymmSndFDerivWithinAt (by
    rw [minSmoothness_of_isRCLikeNormedField]) hS hinterior hmem
  apply hspush.congr_deriv
  calc
    fderivWithin ℝ (fderivWithin ℝ f S) S (t, x) (1, 0) (0, u) =
        fderivWithin ℝ (fderivWithin ℝ f S) S (t, x) (0, u) (1, 0) :=
      hmixed.eq (1, 0) (0, u)
    _ = _ := congrArg (fun A : E →L[ℝ] F => A u) hderivs

theorem hasDerivWithinAt_pullback_coefficient_of_contDiffWithinAt
    {f : ℝ × E → F} {V : F → F}
    {G : F → F →L[ℝ] F →L[ℝ] ℝ} {J : Set ℝ} {U : Set E} {t : ℝ} {x : E}
    (hU : IsOpen U) (hJ : UniqueDiffOn ℝ J) (ht : t ∈ J) (hx : x ∈ U)
    (hinterior : (t, x) ∈ closure (interior (J ×ˢ U)))
    (hf : ContDiffWithinAt ℝ 2 f (J ×ˢ U) (t, x))
    (hV : DifferentiableAt ℝ V (f (t, x)))
    (hG : DifferentiableAt ℝ G (f (t, x)))
    (horbit : ∀ᶠ z in 𝓝 x,
      HasDerivWithinAt (fun s => f (s, z)) (V (f (t, z))) J t)
    (u v : E) :
    HasDerivWithinAt
      (fun s => G (f (s, x))
        (fderiv ℝ (fun z => f (s, z)) x u)
        (fderiv ℝ (fun z => f (s, z)) x v))
      (coordinateLieMetric G V (f (t, x))
        (fderiv ℝ (fun z => f (t, z)) x u)
        (fderiv ℝ (fun z => f (t, z)) x v)) J t := by
  have hbase : HasDerivWithinAt (fun s => G (f (s, x)))
      (fderiv ℝ G (f (t, x)) (V (f (t, x)))) J t :=
    HasFDerivAt.comp_hasDerivWithinAt t (l := G)
      (f := fun s : ℝ => f (s, x)) hG.hasFDerivAt horbit.self_of_nhds
  have hu := hasDerivWithinAt_spatial_fderiv_of_orbit hU hJ ht hx hinterior hf hV horbit u
  have hv := hasDerivWithinAt_spatial_fderiv_of_orbit hU hJ ht hx hinterior hf hV horbit v
  simpa only [coordinateLieMetric, ContinuousLinearMap.add_apply, Function.comp_apply]
    using (hbase.clm_apply hu).clm_apply hv

end PoincareConjecture.ConjugatorLieDerivativeNative

end
