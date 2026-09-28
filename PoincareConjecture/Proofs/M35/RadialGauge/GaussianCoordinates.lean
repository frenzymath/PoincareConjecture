import PoincareConjecture.Proofs.M35.RadialGauge.GaussianIntegration
import Mathlib.MeasureTheory.Integral.Pi









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem continuous_insert_coordinate (i : Fin (n + 1)) (z : Fin n → ℝ) :
    Continuous (fun s : ℝ => i.insertNth (α := fun _ => ℝ) s z) := by
  apply continuous_pi
  intro j
  rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩
  · convert! (continuous_id : Continuous (fun s : ℝ => s)) using 1
    ext s
    simp
  · simpa using (continuous_const : Continuous (fun _ : ℝ => z k))


theorem integral_pi_gaussian_slices (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → F}
    (hf : Integrable f (Measure.pi fun _ => gaussianReal 0 1)) :
    (∫ x, f x ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z : Fin n → ℝ, ∫ s : ℝ, f (i.insertNth s z) ∂gaussianReal 0 1
        ∂Measure.pi fun _ => gaussianReal 0 1 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp := (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun p => f (e.symm p))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
    (hp.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  calc
    _ = ∫ p, f (e.symm p)
        ∂((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
      (hp.integral_comp' f).symm
    _ = _ := by
      simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk] using integral_prod_symm _ hi



theorem integral_pi_gaussian_coordinate_derivative (i : Fin (n + 1))
    {f g : (Fin (n + 1) → ℝ) → F} (hf : Continuous f) (hg : Continuous g)
    {C D : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hdbound : ∀ x, ‖g x‖ ≤ D)
    (hderiv : ∀ (z : Fin n → ℝ) (s : ℝ),
      HasDerivAt (fun a => f (i.insertNth a z)) (g (i.insertNth s z)) s) :
    (∫ x, g x ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ x, x i • f x ∂Measure.pi fun _ => gaussianReal 0 1 := by
  have hmoment : Integrable (fun s : ℝ => ‖s‖) (gaussianReal 0 1) := by
    exact ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).norm
  have hgi : Integrable g (Measure.pi fun _ => gaussianReal 0 1) :=
    (integrable_const D).mono' hg.aestronglyMeasurable (Eventually.of_forall hdbound)
  have hxi : Integrable (fun x : Fin (n + 1) → ℝ => x i • f x)
      (Measure.pi fun _ => gaussianReal 0 1) := by
    apply ((integrable_comp_eval (i := i) hmoment).mul_const C).mono'
      ((continuous_apply i).smul hf).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      change ‖x i • f x‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _))
  rw [integral_pi_gaussian_slices i hgi, integral_pi_gaussian_slices i hxi]
  apply integral_congr_ae
  refine Eventually.of_forall (fun z => ?_)
  have hcz := continuous_insert_coordinate i z
  have hfi : Integrable (fun s : ℝ => f (i.insertNth s z)) (gaussianReal 0 1) :=
    (integrable_const C).mono' (hf.comp hcz).aestronglyMeasurable
      (Eventually.of_forall (fun s => hbound _))
  have hgzi : Integrable (fun s : ℝ => g (i.insertNth s z)) (gaussianReal 0 1) :=
    (integrable_const D).mono' (hg.comp hcz).aestronglyMeasurable
      (Eventually.of_forall (fun s => hdbound _))
  have hsfi : Integrable (fun s : ℝ => s • f (i.insertNth s z)) (gaussianReal 0 1) := by
    apply (hmoment.mul_const C).mono'
      (continuous_id.smul (hf.comp hcz)).aestronglyMeasurable
    exact Eventually.of_forall (fun s => by
      change ‖s • f (i.insertNth s z)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
  simpa using integral_standardGaussian_derivative (hderiv z) hfi hgzi hsfi

end PoincareConjecture.M35.RadialGauge
