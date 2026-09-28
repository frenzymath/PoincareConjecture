import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Energy
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakDerivativeLimit







noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace Poincare.Analysis.Elliptic


def lipschitzPartialL2 {d : ℕ} {O : Set (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure (volume.restrict O)] (hO : IsOpen O)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) (i : Fin d) : Lp ℝ 2 (volume.restrict O) :=
  ((Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn hO hu
    (EuclideanSpace.single i 1)).mono_exponent (p := 2) le_top).toLp _

theorem coeFn_lipschitzPartialL2 {d : ℕ} {O : Set (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure (volume.restrict O)] (hO : IsOpen O)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) (i : Fin d) :
    lipschitzPartialL2 hO hu i =ᵐ[volume.restrict O]
      fun x => fderiv ℝ u x (EuclideanSpace.single i 1) :=
  MemLp.coeFn_toLp _


theorem norm_toLp_sub_sq_eq_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub hf hg, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf.sub hg).coeFn_toLp] with x hx
  rw [hx]
  simp only [Pi.sub_apply, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]


theorem norm_toLp_sub_sq_le_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {U O : Set X}
    (hU : MeasurableSet U) (hO : MeasurableSet O) (hUO : U ⊆ O)
    {f g energy : X → ℝ}
    (hf : MemLp f 2 (μ.restrict U)) (hg : MemLp g 2 (μ.restrict U))
    (he : IntegrableOn energy O μ)
    (he0 : ∀ x ∈ O, 0 ≤ energy x)
    (hbound : ∀ x ∈ U, (f x - g x) ^ 2 ≤ energy x) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 ≤ ∫ x in O, energy x ∂μ := by
  rw [norm_toLp_sub_sq_eq_integral]
  have hsq : IntegrableOn (fun x => (f x - g x) ^ 2) U μ := by
    have heq : (fun x => (f x - g x) ^ 2) = (f - g) * (f - g) := by
      funext x
      simp only [pow_two, Pi.mul_apply, Pi.sub_apply]
    rw [IntegrableOn, heq]
    exact (hf.sub hg).integrable_mul (hf.sub hg)
  refine (setIntegral_mono_on hsq (he.mono_set hUO) hU hbound).trans ?_
  apply setIntegral_mono_set he
  · filter_upwards [ae_restrict_mem hO] with x hx
    exact he0 x hx
  · exact Eventually.of_forall hUO

end Poincare.Analysis.Elliptic
