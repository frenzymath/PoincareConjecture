import PoincareConjecture.Proofs.M35.RadialGauge.SmoothEuclideanGauge
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem euclideanGauge_hasDerivAt_time
    {u : ℝ → V → ℝ} {t q : ℝ} {x : V}
    (hu : HasDerivAt (fun s => u s x) q t) :
    HasDerivAt (fun s => euclideanGauge (u s) x)
      ((Real.exp (u t x) * q) • x) t := by
  exact hu.exp.smul_const x

theorem euclideanGauge_fderiv_hasDerivAt_time
    {u : ℝ → V → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hs : ∀ s ∈ J, ContDiff ℝ ∞ (u s))
    {t q : ℝ} {x : V} {Q : V →L[ℝ] ℝ} (ht : t ∈ J)
    (hu : HasDerivAt (fun s => u s x) q t)
    (hdu : HasDerivAt (fun s => fderiv ℝ (u s) x) Q t) :
    HasDerivAt (fun s => fderiv ℝ (euclideanGauge (u s)) x)
      ((Real.exp (u t x) * q) • ContinuousLinearMap.id ℝ V +
        ((Real.exp (u t x) * q) • fderiv ℝ (u t) x +
          Real.exp (u t x) • Q).smulRight x) t := by
  let L : (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] V :=
    (ContinuousLinearMap.smulRightL ℝ V V).flip x
  have hL : HasDerivAt (fun s => Real.exp (u s x) • ContinuousLinearMap.id ℝ V)
      ((Real.exp (u t x) * q) • ContinuousLinearMap.id ℝ V) t :=
    hu.exp.smul_const (ContinuousLinearMap.id ℝ V)
  have hR : HasDerivAt (fun s => (Real.exp (u s x) • fderiv ℝ (u s) x).smulRight x)
      (((Real.exp (u t x) * q) • fderiv ℝ (u t) x +
        Real.exp (u t x) • Q).smulRight x) t :=
    L.hasFDerivAt.comp_hasDerivAt t ((hu.exp.smul hdu).congr_deriv (add_comm _ _))
  apply (hL.add hR).congr_of_eventuallyEq
  filter_upwards [hJ.mem_nhds ht] with s hs'
  exact (euclideanGauge_hasFDerivAt ((hs s hs').differentiable (by simp) x)).fderiv

theorem euclideanGauge_fderiv_joint_c1
    {u : ℝ → V → ℝ} {J : Set ℝ}
    (hs : ∀ s ∈ J, ContDiff ℝ ∞ (u s))
    (hu : ContDiffOn ℝ 1 (Function.uncurry u) (J ×ˢ univ))
    (hdu : ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (u p.1) p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × V => fderiv ℝ (euclideanGauge (u p.1)) p.2)
      (J ×ˢ univ) := by
  have hL := hu.exp.smul (contDiffOn_const (c := ContinuousLinearMap.id ℝ V))
  have hR := ((ContinuousLinearMap.smulRightL ℝ V V).contDiff.comp_contDiffOn
    (hu.exp.smul hdu)).clm_apply contDiffOn_snd
  apply (hL.add hR).congr
  intro p hp
  exact (euclideanGauge_hasFDerivAt ((hs p.1 hp.1).differentiable (by simp) p.2)).fderiv

end PoincareConjecture.M35.RadialGauge
