import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeDiskEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeContinuous
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTargetCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def m64EuclideanInterpolator (z : ℝ × (E × E)) : E :=
  (1 - z.1) • z.2.1 + z.1 • z.2.2

theorem m64EuclideanInterpolator_contDiff :
    ContDiff ℝ ∞ (m64EuclideanInterpolator (m := m)) := by
  exact ((contDiff_const.sub contDiff_fst).smul contDiff_snd.fst).add
    (contDiff_fst.smul contDiff_snd.snd)

theorem m64EuclideanInterpolator_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 m).prod (𝓡 m))) (𝓡 m) 1
      (m64EuclideanInterpolator (m := m)) := by
  exact ((contMDiff_const.sub contMDiff_fst).smul contMDiff_snd.fst).add
    (contMDiff_fst.smul contMDiff_snd.snd)

theorem m64EuclideanInterpolator_speed (s : ℝ) (p q : E) :
    (RiemannianMetric.euclideanMetric m).tangentNorm (m64EuclideanInterpolator (s, p, q))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 m) (fun t => m64EuclideanInterpolator (t, p, q)) s 1) =
        ((RiemannianMetric.euclideanMetric m).edist p q).toReal := by
  have hd : HasDerivAt (fun t : ℝ => m64EuclideanInterpolator (t, p, q)) (q - p) s := by
    have h := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).smul_const p).add
      ((hasDerivAt_id s).smul_const q)
    simpa +instances only [m64EuclideanInterpolator, Pi.add_apply, Pi.sub_apply, id_eq,
      zero_sub, one_smul, neg_smul, one_mul, neg_add_eq_sub] using! h
  have hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 m)
      (fun t => m64EuclideanInterpolator (t, p, q)) s 1 = q - p := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hd.deriv
  rw [hv]
  simp +instances only [RiemannianMetric.euclideanMetric_tangentNorm,
    RiemannianMetric.euclideanMetric_edist, edist_dist, dist_eq_norm, norm_sub_rev]
  exact (ENNReal.toReal_ofReal (norm_nonneg _)).symm

theorem m64EuclideanInterpolator_last_column (s : ℝ) (p q v : E) :
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 m).prod (𝓡 m))) (𝓡 m) m64EuclideanInterpolator
      (s, p, q) (0, 0, v) = s • v := by
  have hH := (m64EuclideanInterpolator_contMDiff (m := m)).mdifferentiable (by simp) (s, p, q)
  have hs : MDifferentiableAt ((𝓡 m).prod (𝓡 m)) (𝓡 m)
      (fun pq : E × E => m64EuclideanInterpolator (s, pq)) (p, q) :=
    hH.comp (p, q) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [mfderiv_prod_eq_add_apply hH, map_zero, zero_add,
    mfderiv_prod_eq_add_apply hs, map_zero, zero_add]
  have hd := (hasFDerivAt_const ((1 - s) • p) q).add
    ((hasFDerivAt_id (𝕜 := ℝ) q).const_smul s)
  have heq := congrArg (fun D => D v) hd.fderiv
  simpa +instances only [m64EuclideanInterpolator, mfderiv_eq_fderiv, add_apply,
    zero_apply, zero_add, smul_apply, ContinuousLinearMap.id_apply,
    Pi.add_apply, id_eq] using! heq

def m64EuclideanCone (w : ℝ → E) : LoopPlane → E :=
  m64LocalConeDiskMap m64EuclideanInterpolator (w 0) w

theorem m64EuclideanCone_continuous {w : ℝ → E}
    (hw : Continuous w) (hperiod : Function.Periodic w curvePeriod) :
    Continuous (m64EuclideanCone w) :=
  m64LocalConeDiskMap_continuous m64EuclideanInterpolator (w 0) w hw hperiod
    (fun x => by simp [m64EuclideanInterpolator])
    (fun _ _ _ => m64EuclideanInterpolator_contDiff.continuous.continuousAt)

theorem m64EuclideanCone_tendsto (w : ℕ → ℝ → E) (u : ℝ → E)
    (hw : ∀ x, Tendsto (fun j => w j x) atTop (𝓝 (u x))) (p : LoopPlane) :
    Tendsto (fun j => m64EuclideanCone (w j) p) atTop (𝓝 (m64EuclideanCone u p)) :=
  m64LocalConeDiskMap_tendsto m64EuclideanInterpolator (fun j => w j 0) w (u 0) u
    (hw 0) hw (fun _ _ _ => m64EuclideanInterpolator_contDiff.continuous.continuousAt) p

theorem m64EuclideanCone_contDiff {w : ℝ → E}
    (hw : ContDiff ℝ 1 w) (hperiod : Function.Periodic w curvePeriod) :
    ContDiff ℝ 1 (m64EuclideanCone w) := by
  apply contMDiff_iff_contDiff.mp
  exact m64LocalConeDiskMap_contMDiff m64EuclideanInterpolator (w 0) w hw.contMDiff hperiod
    (fun x => by simp [m64EuclideanInterpolator])
    (fun _ _ _ => (m64EuclideanInterpolator_contMDiff (m := m)).contMDiffAt)

theorem m64EuclideanCone_boundary {w : ℝ → E}
    (hperiod : Function.Periodic w curvePeriod) (x : ℝ) :
    m64EuclideanCone w (angularPoint x) = w x :=
  m64LocalConeDiskMap_boundary m64EuclideanInterpolator (w 0) w hperiod
    (fun x => by simp [m64EuclideanInterpolator]) x

theorem m64EuclideanCone_range {w : ℝ → E} {z : E} {r : ℝ}
    (hw : ∀ x, w x ∈ closedBall z r) (p : LoopPlane) :
    m64EuclideanCone w p ∈ closedBall z r := by
  classical
  by_cases hp : p = 0
  · simpa only [m64EuclideanCone, m64LocalConeDiskMap, if_pos hp] using hw 0
  · rw [m64EuclideanCone, m64LocalConeDiskMap, if_neg hp]
    obtain ⟨ht0, ht1⟩ := diskTimeProfile_mem_Icc ‖p‖
    exact (convex_closedBall z r) (hw 0) (hw (m60PlaneAngle p))
      (by linarith : 0 ≤ 1 - (1 - diskTimeProfile ‖p‖))
      (by linarith : 0 ≤ 1 - diskTimeProfile ‖p‖) (by ring)

end PoincareConjecture
