import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSobolevJets
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslation
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

open AddCircle Filter
open scoped Topology ENNReal

namespace PoincareConjecture.M63

variable {L : ℝ}

noncomputable def periodicSpectralTranslation (a : ℝ) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  lp.mapCLM 2 (fun n : ℤ => ContinuousLinearMap.mul ℂ ℂ
    (fourier n (-(a : AddCircle L)))) zero_le_one (fun n => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro z
      change ‖fourier n (-(a : AddCircle L)) * z‖ ≤ 1 * ‖z‖
      rw [norm_mul, fourier_apply, Circle.norm_coe])

theorem periodicSpectralTranslation_spec (a : ℝ) (u : lp (fun _ : ℤ => ℂ) 2) :
    (∀ n : ℤ, periodicSpectralTranslation (L := L) a u n =
      fourier n (-(a : AddCircle L)) * u n) ∧
      ‖periodicSpectralTranslation (L := L) a u‖ = ‖u‖ := by
  have hn (n : ℤ) : ‖periodicSpectralTranslation (L := L) a u n‖ = ‖u n‖ := by
    change ‖fourier n (-(a : AddCircle L)) * u n‖ = ‖u n‖
    rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  refine ⟨fun _ => rfl, le_antisymm ?_ ?_⟩
  · exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun n => (hn n).le)
  · exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun n => (hn n).symm.le)

theorem periodicSpectralTranslation_group :
    periodicSpectralTranslation (L := L) 0 = ContinuousLinearMap.id ℂ _ ∧
      ∀ a b : ℝ, periodicSpectralTranslation (L := L) (a + b) =
        (periodicSpectralTranslation (L := L) a).comp
          (periodicSpectralTranslation (L := L) b) := by
  constructor
  · ext u n
    change fourier n (-(0 : AddCircle L)) * u n = u n
    rw [neg_zero, fourier_eval_zero, one_mul]
  · intro a b
    ext u n
    change fourier n (-((a + b : ℝ) : AddCircle L)) * u n =
      fourier n (-(a : AddCircle L)) * (fourier n (-(b : AddCircle L)) * u n)
    simp_rw [AddCircle.coe_add, neg_add, fourier_apply, zsmul_add,
      toCircle_add, Circle.coe_mul]
    ring

theorem continuous_periodicSpectralTranslation :
    Continuous (fun p : ℝ × lp (fun _ : ℤ => ℂ) 2 =>
      periodicSpectralTranslation (L := L) p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro a
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, ← map_sub, (periodicSpectralTranslation_spec a (u - v)).2,
      NNReal.coe_one, one_mul, dist_eq_norm]
  · intro u
    apply continuous_iff_continuousAt.mpr
    intro a0
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hu : Summable (fun n : ℤ => ‖u n‖ ^ 2) := by
      simpa using (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    have hp (a : ℝ) (n : ℤ) : ‖fourier n (-(a : AddCircle L))‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    have hconv : Tendsto (fun a : ℝ => ∑' n : ℤ,
        ‖(fourier n (-(a : AddCircle L)) - fourier n (-(a0 : AddCircle L))) * u n‖ ^ 2)
        (𝓝 a0) (𝓝 (∑' _n : ℤ, (0 : ℝ))) := by
      apply tendsto_tsum_of_dominated_convergence (hu.mul_left 4)
      · intro n
        have hc : Continuous (fun a : ℝ =>
            ‖(fourier n (-(a : AddCircle L)) - fourier n (-(a0 : AddCircle L))) * u n‖ ^ 2) :=
          ((((fourier n).continuous.comp (AddCircle.continuous_mk' L).neg).sub
            continuous_const).mul continuous_const).norm.pow 2
        simpa using hc.continuousAt.tendsto (x := a0)
      · apply Eventually.of_forall
        intro a n
        have hd : ‖fourier n (-(a : AddCircle L)) -
            fourier n (-(a0 : AddCircle L))‖ ≤ 2 := by
          simpa only [hp, one_add_one_eq_two] using
            norm_sub_le (fourier n (-(a : AddCircle L)))
              (fourier n (-(a0 : AddCircle L)))
        rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
        calc
          _ ≤ 2 ^ 2 * ‖u n‖ ^ 2 := mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) hd 2) (sq_nonneg _)
          _ = 4 * ‖u n‖ ^ 2 := by norm_num
    have hnorm (a : ℝ) :
        ‖periodicSpectralTranslation (L := L) a u - periodicSpectralTranslation (L := L) a0 u‖ ^ 2 =
          ∑' n : ℤ, ‖(fourier n (-(a : AddCircle L)) -
            fourier n (-(a0 : AddCircle L))) * u n‖ ^ 2 := by
      calc
        _ = ∑' n : ℤ, ‖(periodicSpectralTranslation (L := L) a u -
            periodicSpectralTranslation (L := L) a0 u) n‖ ^ 2 := by
          simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
            (periodicSpectralTranslation (L := L) a u - periodicSpectralTranslation (L := L) a0 u)
        _ = _ := by
          congr 1
          funext n
          change ‖fourier n (-(a : AddCircle L)) * u n -
            fourier n (-(a0 : AddCircle L)) * u n‖ ^ 2 = _
          rw [sub_mul]
    simp only [tsum_zero] at hconv
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
    simpa only [Function.comp_def, ← hnorm, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hsqrt

variable [Fact (0 < L)]

theorem weightedFourier_periodicSpectralTranslation
    (w u : lp (fun _ : ℤ => ℂ) 2) (a : ℝ) :
    weightedFourier (L := L) w (periodicSpectralTranslation (L := L) a u) =
      periodicTranslation a (weightedFourier w u) := by
  let A := (periodicTranslation (L := L) (E := ℂ) a).toContinuousLinearEquiv.toContinuousLinearMap
  have hs := A.hasSum (weightedFourier_hasSum (L := L) w u)
  have hterm (n : ℤ) : A ((w n * u n) • fourier n) =
      (w n * periodicSpectralTranslation (L := L) a u n) • fourier n := by
    ext x
    change (w n * u n) * fourier n (x - (a : AddCircle L)) =
      (w n * (fourier n (-(a : AddCircle L)) * u n)) * fourier n x
    simp_rw [sub_eq_add_neg, fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
    ring
  simp_rw [hterm] at hs
  exact (weightedFourier_hasSum w (periodicSpectralTranslation (L := L) a u)).unique hs

theorem periodicSobolevJet_periodicSpectralTranslation (k j : ℕ) (hj : j ≤ k)
    (u : lp (fun _ : ℤ => ℂ) 2) (a : ℝ) :
    periodicSobolevJet (L := L) k j hj (periodicSpectralTranslation (L := L) a u) =
      periodicTranslation a (periodicSobolevJet (L := L) k j hj u) :=
  weightedFourier_periodicSpectralTranslation
    ⟨periodicSobolevMoment L k j, (periodicSobolevMoment_bound hj).2⟩ u a

end PoincareConjecture.M63
