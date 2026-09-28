import PoincareConjecture.Proofs.M14.Mathlib.FiniteEnergyBlend










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

open Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]





theorem oneSidedBlend_energy_le {f g : ℝ → E} {b d K : ℝ}
    (hd : 0 < d) (hK : 0 ≤ K)
    (hKb : ∀ r ∈ Icc (-1 : ℝ) 1, ‖deriv smoothJoinCutoff r‖ ≤ K)
    (hf : ContinuousOn f (Icc (b - 2 * d) b))
    (hg : ContinuousOn g (Icc (b - 2 * d) b))
    (hdf : DifferentiableOn ℝ f (Ioo (b - 2 * d) b))
    (hdg : DifferentiableOn ℝ g (Ioo (b - 2 * d) b))
    (hEf : MemLp (deriv f) 2 (volume.restrict (Icc (b - 2 * d) b)))
    (hEg : MemLp (deriv g) 2 (volume.restrict (Icc (b - 2 * d) b)))
    (heq : f b = g b) :
    IntervalIntegrable
        (fun s => ‖deriv (smoothJoinBlend f g (b - 3 * d / 2) (d / 2)) s‖ ^ 2)
        volume (b - 2 * d) (b - d) ∧
      (∫ s in (b - 2 * d)..(b - d),
        ‖deriv (smoothJoinBlend f g (b - 3 * d / 2) (d / 2)) s‖ ^ 2) ≤
        (12 + 48 * K ^ 2) *
          ((∫ s in (b - 2 * d)..b, ‖deriv f s‖ ^ 2) +
            ∫ s in (b - 2 * d)..b, ‖deriv g s‖ ^ 2) := by
  let e := (∫ s in (b - 2 * d)..b, ‖deriv f s‖ ^ 2) +
    ∫ s in (b - 2 * d)..b, ‖deriv g s‖ ^ 2
  let H := fun s => 12 * (‖deriv f s‖ ^ 2 + ‖deriv g s‖ ^ 2) + (48 * K ^ 2 / d) * e
  let B := fun s => ‖deriv (smoothJoinBlend f g (b - 3 * d / 2) (d / 2)) s‖ ^ 2
  have hab : b - 2 * d ≤ b := by linarith
  have hlr : b - 2 * d ≤ b - d := by linarith
  have hright : b - d ≤ b := by linarith
  have hIf : IntervalIntegrable (fun s => ‖deriv f s‖ ^ 2) volume (b - 2 * d) b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((memLp_two_iff_integrable_sq_norm hEf.aestronglyMeasurable).mp hEf)
  have hIg : IntervalIntegrable (fun s => ‖deriv g s‖ ^ 2) volume (b - 2 * d) b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((memLp_two_iff_integrable_sq_norm hEg.aestronglyMeasurable).mp hEg)
  have hsub : uIcc (b - 2 * d) (b - d) ⊆ uIcc (b - 2 * d) b := by
    rw [uIcc_of_le hlr, uIcc_of_le hab]
    exact Icc_subset_Icc_right hright
  have hif := hIf.mono_set hsub
  have hig := hIg.mono_set hsub
  have hH : IntervalIntegrable H volume (b - 2 * d) (b - d) :=
    ((hif.add hig).const_mul 12).add intervalIntegrable_const
  have hpoint (s : ℝ) (hs : s ∈ Ioo (b - 2 * d) (b - d)) : B s ≤ H s :=
    oneSidedBlend_deriv_sq_le hd hK hKb hf hg hdf hdg hEf hEg heq hs
  have hB : IntervalIntegrable B volume (b - 2 * d) (b - d) := by
    apply hH.mono_fun' ((aestronglyMeasurable_deriv _ _).norm.pow 2)
    rw [uIoc_of_le hlr, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    change |B s| ≤ H s
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hpoint s hs
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hlr hB hH hpoint
  have hformula : (∫ s in (b - 2 * d)..(b - d), H s) =
      12 * ((∫ s in (b - 2 * d)..(b - d), ‖deriv f s‖ ^ 2) +
        ∫ s in (b - 2 * d)..(b - d), ‖deriv g s‖ ^ 2) + 48 * K ^ 2 * e := by
    dsimp only [H]
    rw [intervalIntegral.integral_add ((hif.add hig).const_mul 12) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add hif hig,
      intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    field_simp [hd.ne']
    ring
  have hfle := intervalIntegral.integral_mono_interval le_rfl hlr hright
    (ae_of_all _ (fun s => sq_nonneg ‖deriv f s‖)) hIf
  have hgle := intervalIntegral.integral_mono_interval le_rfl hlr hright
    (ae_of_all _ (fun s => sq_nonneg ‖deriv g s‖)) hIg
  refine ⟨hB, hbound.trans ?_⟩
  rw [hformula]
  change _ ≤ (12 + 48 * K ^ 2) * e
  dsimp only [e]
  nlinarith

end PoincareConjecture.M14
