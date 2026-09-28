import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open scoped ContDiff Topology

namespace PoincareConjecture.ConjugatorLieDerivativeNative

section Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem spatial_fderiv_eq {f : ℝ × E → F} {t : ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (t, x)) :
    fderiv ℝ (fun z => f (t, z)) x =
      (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  exact (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv

theorem hasDerivAt_spatial_fderiv_of_orbit
    {f : ℝ × E → F} {V : F → F} {J : Set ℝ} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (t, x))
    (hJ : UniqueDiffWithinAt ℝ J t)
    (hV : DifferentiableAt ℝ V (f (t, x)))
    (horbit : ∀ᶠ z in 𝓝 x,
      HasDerivWithinAt (fun s => f (s, z)) (V (f (t, z))) J t)
    (u : E) :
    HasDerivAt (fun s => fderiv ℝ (fun z => f (s, z)) x u)
      (fderiv ℝ V (f (t, x)) (fderiv ℝ (fun z => f (t, z)) x u)) t := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (t, x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hlocal : ∀ᶠ q in 𝓝 (t, x), DifferentiableAt ℝ f q :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt two_ne_zero
  have htx : ContinuousAt (fun s : ℝ => (s, x)) t := by fun_prop
  have htz : ContinuousAt (fun z : E => (t, z)) x := by fun_prop
  have htime : (fun z => fderiv ℝ f (t, z) (1, 0)) =ᶠ[𝓝 x]
      (fun z => V (f (t, z))) := by
    filter_upwards [htz hlocal, horbit] with z hz hode
    have hcurve : HasDerivAt (fun s => f (s, z))
        (fderiv ℝ f (t, z) (1, 0)) t := by
      have hline : HasDerivAt (fun s : ℝ => (s, z)) (1, 0) t := by
        simpa using HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t z)
      exact HasFDerivAt.comp_hasDerivAt t (f := fun s : ℝ => (s, z))
        hz.hasFDerivAt hline
    exact hJ.eq_deriv _ hcurve.hasDerivWithinAt hode
  have hline : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t := by
    simpa using HasDerivAt.prodMk (hasDerivAt_id t) (hasDerivAt_const t x)
  have hDtime := (HasFDerivAt.comp_hasDerivAt t (f := fun s : ℝ => (s, x))
    hfd.hasFDerivAt hline).clm_apply
      (hasDerivAt_const t ((0, u) : ℝ × E))
  have hspatial :
      (fun s => fderiv ℝ (fun z => f (s, z)) x u) =ᶠ[𝓝 t]
        (fun s => fderiv ℝ f (s, x) (0, u)) := by
    filter_upwards [htx hlocal] with s hs
    rw [spatial_fderiv_eq hs]
    rfl
  have hspush : HasDerivAt (fun s => fderiv ℝ (fun z => f (s, z)) x u)
      (fderiv ℝ (fderiv ℝ f) (t, x) (1, 0) (0, u)) t := by
    apply HasDerivAt.congr_of_eventuallyEq _ hspatial
    simpa only [map_zero, add_zero, Function.comp_apply] using hDtime
  have hspaceTime : HasFDerivAt (fun z => fderiv ℝ f (t, z) (1, 0))
      (((fderiv ℝ (fderiv ℝ f) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)).flip (1, 0)) x := by
    have h := (hfd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × E) x)
    simpa using h
  have hcomp : HasFDerivAt (fun z => V (f (t, z)))
      ((fderiv ℝ V (f (t, x))).comp (fderiv ℝ (fun z => f (t, z)) x)) x := by
    exact hV.hasFDerivAt.comp x
      ((hf.differentiableAt two_ne_zero).comp x
        (hasFDerivAt_prodMk_right t x).differentiableAt).hasFDerivAt
  have hderivs := (hspaceTime.congr_of_eventuallyEq htime.symm).unique hcomp
  have hmixed := hf.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField])
  apply hspush.congr_deriv
  calc
    fderiv ℝ (fderiv ℝ f) (t, x) (1, 0) (0, u) =
        fderiv ℝ (fderiv ℝ f) (t, x) (0, u) (1, 0) :=
      hmixed.eq (1, 0) (0, u)
    _ = _ := congrArg (fun A : E →L[ℝ] F => A u) hderivs

def coordinateLieMetric (G : F → F →L[ℝ] F →L[ℝ] ℝ) (V : F → F)
    (z u v : F) : ℝ :=
  fderiv ℝ G z (V z) u v + G z (fderiv ℝ V z u) v +
    G z u (fderiv ℝ V z v)

theorem hasDerivWithinAt_pullback_coefficient
    {f : ℝ × E → F} {V : F → F}
    {G : F → F →L[ℝ] F →L[ℝ] ℝ} {J : Set ℝ} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (t, x))
    (hJ : UniqueDiffWithinAt ℝ J t)
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
  have hu := (hasDerivAt_spatial_fderiv_of_orbit hf hJ hV horbit u).hasDerivWithinAt (s := J)
  have hv := (hasDerivAt_spatial_fderiv_of_orbit hf hJ hV horbit v).hasDerivWithinAt (s := J)
  simpa only [coordinateLieMetric, ContinuousLinearMap.add_apply, Function.comp_apply]
    using (hbase.clm_apply hu).clm_apply hv

theorem coordinateLieMetric_neg
    (G : F → F →L[ℝ] F →L[ℝ] ℝ) (W : F → F) (z u v : F) :
    coordinateLieMetric G (fun y => -W y) z u v =
      -coordinateLieMetric G W z u v := by
  have hneg : fderiv ℝ (fun y => -W y) z = -fderiv ℝ W z := fderiv_neg
  simp only [coordinateLieMetric, hneg, neg_apply, map_neg]
  ring

end Euclidean

end PoincareConjecture.ConjugatorLieDerivativeNative

end
