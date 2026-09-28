import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CutoffEnergy
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.CompactApproximation
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.InteriorCutoff
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Cutoff
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Restriction
import PoincareConjecture.Proofs.M03.Existence.EuclideanRellichNative

set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped Topology

namespace PoincareConjecture

open EuclideanTranslationNative EuclideanMollificationNative EuclideanRellichNative

theorem m65C1_disk_totallyBounded {d : ℕ} {I : Type*}
    (f : I → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hfL2 : ∀ n, MemLp (f n) 2 (volume.restrict (closedBall 0 1)))
    (hdL2 : ∀ n (i : Fin d), MemLp
      (fun x => fderiv ℝ (f n) x (EuclideanSpace.single i (1 : ℝ))) 2
        (volume.restrict (closedBall 0 1)))
    {C D : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n x, x ∈ closedBall 0 1 → |f n x| ≤ C)
    (henergy : ∀ n, (∑ i : Fin d, ∫ x in closedBall 0 1,
      (fderiv ℝ (f n) x (EuclideanSpace.single i (1 : ℝ))) ^ 2) ≤ D ^ 2) :
    TotallyBounded (range fun n => (hfL2 n).toLp (f n)) := by
  classical
  let S : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1
  let mu : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict S
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).measure_lt_top.ne
  let u (n : I) : Lp ℝ 2 mu := (hfL2 n).toLp (f n)
  have hconst : MemLp (fun _ : EuclideanSpace ℝ (Fin d) => C) 2 mu := memLp_const C
  let R : ℝ := ‖hconst.toLp (fun _ => C)‖
  have hR : 0 ≤ R := norm_nonneg _
  have hu (n : I) : u n =ᵐ[mu] f n := (hfL2 n).coeFn_toLp
  have huC (n : I) : ∀ᵐ x ∂mu, ‖u n x‖ ≤ C := by
    filter_upwards [hu n, ae_restrict_mem measurableSet_closedBall] with x hx hxs
    simpa only [hx, Real.norm_eq_abs] using hbound n x hxs
  have huR (n : I) : ‖u n‖ ≤ R := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [huC n, hconst.coeFn_toLp] with x hx hc
    simpa only [hc, Real.norm_eq_abs, abs_of_nonneg hC] using hx
  have hvalue (n : I) : ∫ x in S, (f n x) ^ 2 ≤ R ^ 2 := by
    have heq := (hfL2 n).norm_toLp_sq
    simp only [Real.norm_eq_abs, sq_abs] at heq
    rw [← heq]
    exact (sq_le_sq₀ (norm_nonneg _) hR).mpr (huR n)
  change TotallyBounded (range u)
  apply Metric.totallyBounded_range_of_uniform_approximation
  intro eps heps
  obtain ⟨theta, hthetaOut, hsmall⟩ :=
    ContDiffBump.exists_integral_sub_one_sq_lt
      (E := EuclideanSpace ℝ (Fin d)) volume
      (eps := eps ^ 2 / (C ^ 2 + 1)) (by positivity)
  have hthetaS : tsupport theta ⊆ S := by
    rw [theta.tsupport_eq]
    exact closedBall_subset_closedBall hthetaOut.le
  have hthetaAbs (x : EuclideanSpace ℝ (Fin d)) : |theta x| ≤ 1 := by
    rw [abs_of_nonneg theta.nonneg]
    exact theta.le_one
  obtain ⟨B0, hB0⟩ := (theta.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((theta.contDiff : ContDiff ℝ 1 theta).continuous_fderiv one_ne_zero)
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hderiv (x : EuclideanSpace ℝ (Fin d)) : ‖fderiv ℝ theta x‖ ≤ B :=
    (hB0 x).trans (le_max_left _ _)
  let g (n : I) := fun x => theta x * f n x
  have hg (n : I) : ContDiff ℝ 1 (g n) := theta.contDiff.mul (hf n)
  have hgc (n : I) : HasCompactSupport (g n) := theta.hasCompactSupport.mul_right
  have hgL2 (n : I) : MemLp (g n) 2 volume :=
    (hg n).continuous.memLp_of_hasCompactSupport (hgc n)
  let v (n : I) : Lp ℝ 2 mu := ((hgL2 n).restrict S).toLp (g n)
  have hv (n : I) : v n =ᵐ[mu] g n := ((hgL2 n).restrict S).coeFn_toLp
  have hgzero (n : I) (x : EuclideanSpace ℝ (Fin d)) (hx : x ∉ S) : g n x = 0 := by
    have hdist : 1 < dist x 0 := not_le.mp hx
    simp only [g, theta.zero_of_le_dist (hthetaOut.le.trans hdist.le), zero_mul]
  have hvu (n : I) : ‖v n‖ ≤ ‖u n‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hv n, hu n] with x hx hy
    simp only [hx, hy, g, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hthetaAbs x)
  have hgR (n : I) : ‖(hgL2 n).toLp (g n)‖ ≤ R := by
    rw [← (hgL2 n).norm_toLp_restrict_eq_of_zero measurableSet_closedBall (hgzero n)]
    exact (hvu n).trans (huR n)
  have hgD (n : I) : gradientEnergy (g n) ≤
      (Real.sqrt (2 * D ^ 2 + 2 * (d : ℝ) * B ^ 2 * R ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    exact m65C1_cutoff_gradientEnergy_le measurableSet_closedBall (hf n) theta.contDiff
      theta.hasCompactSupport hthetaS hthetaAbs hB hderiv
      (hfL2 n) (hdL2 n) (hvalue n) (henergy n)
  have htbGlobal : TotallyBounded (range fun n => (hgL2 n).toLp (g n)) := by
    apply totallyBounded_supported_C1 theta.hasCompactSupport
      (D := Real.sqrt (2 * D ^ 2 + 2 * (d : ℝ) * B ^ 2 * R ^ 2))
      (Real.sqrt_nonneg _) (R := R)
    · rintro _ ⟨n, rfl⟩
      exact hgR n
    · rintro _ ⟨n, rfl⟩
      refine ⟨g n, hg n, hgL2 n, ?_, ?_, rfl, hgD n⟩
      · intro i
        exact ((hg n).continuous_fderiv one_ne_zero).clm_apply continuous_const
          |>.memLp_of_hasCompactSupport ((hgc n).fderiv_apply ℝ _)
      · intro x hx
        have hz : theta x = 0 := Function.notMem_support.mp fun h => hx (subset_closure h)
        simp only [g, hz, zero_mul]
  have htb : TotallyBounded (range v) := by
    have himage := htbGlobal.image
      (LpToLpRestrictCLM (EuclideanSpace ℝ (Fin d)) ℝ ℝ volume 2 S).uniformContinuous
    simpa only [← range_comp, Function.comp_def, LpToLpRestrictCLM_toLp, v] using himage
  refine ⟨v, htb, ?_⟩
  intro n
  have hthetaMeas : AEStronglyMeasurable theta mu := theta.continuous.aestronglyMeasurable
  have hthetaAE : ∀ᵐ x ∂mu, |theta x| ≤ 1 := ae_of_all mu hthetaAbs
  have hvcut : v n = ((Lp.memLp (u n)).smul_cutoff hthetaMeas hthetaAE).toLp
      (fun x => theta x • u n x) := by
    apply Lp.ext
    filter_upwards [hv n, hu n,
      ((Lp.memLp (u n)).smul_cutoff hthetaMeas hthetaAE).coeFn_toLp] with x hx hy hc
    exact hx.trans ((show g n x = theta x • u n x by rw [hy]; rfl).trans hc.symm)
  have herr := Lp.norm_sub_cutoff_sq_le (u n) hthetaMeas hthetaAE hC (huC n)
  rw [← hvcut] at herr
  have hnonneg : 0 ≤ ∫ x in S, (1 - theta x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hsmall' := (lt_div_iff₀ (show 0 < C ^ 2 + 1 by positivity)).mp hsmall
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) heps.le).mp
  change ‖u n - v n‖ ^ 2 ≤ C ^ 2 * ∫ x in S, (1 - theta x) ^ 2 at herr
  nlinarith

end PoincareConjecture
