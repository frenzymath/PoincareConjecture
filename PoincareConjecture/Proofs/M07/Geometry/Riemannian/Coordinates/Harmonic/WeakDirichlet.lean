import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Heat.Dirichlet.Resolvent
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

set_option autoImplicit false
set_option maxSynthPendingDepth 12

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

def gradientEnergy (D : LeviCivitaData g) (Ω : Set M) :
    H1Zero D Ω →L[ℝ] H1Zero D Ω →L[ℝ] ℝ :=
  innerSL ℝ - (innerSL ℝ).bilinearComp (toL2 D Ω) (toL2 D Ω)

@[simp] theorem gradientEnergy_apply (v w : H1Zero D Ω) :
    gradientEnergy D Ω v w = ⟪v, w⟫_ℝ - ⟪toL2 D Ω v, toL2 D Ω w⟫_ℝ := rfl

theorem gradientEnergy_symm (v w : H1Zero D Ω) :
    gradientEnergy D Ω v w = gradientEnergy D Ω w v := by
  simp only [gradientEnergy_apply, real_inner_comm]

@[simp] theorem gradientEnergy_coe (f h : EnergyTest D Ω) :
    gradientEnergy D Ω (f : H1Zero D Ω) (h : H1Zero D Ω) =
      ∫ x, g.inner x (D.gradient f x) (D.gradient h x) ∂g.volumeMeasure := by
  simp only [gradientEnergy_apply, Completion.inner_coe, toL2_coe,
    EnergyTest.inner_eq, testToL2_inner, energyInner, add_sub_cancel_left]

theorem gradientEnergy_self_nonneg (v : H1Zero D Ω) :
    0 ≤ gradientEnergy D Ω v v := by
  rw [gradientEnergy_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (norm_toL2_le v) 2)

theorem gradientEnergy_self_le_norm_sq (v : H1Zero D Ω) :
    gradientEnergy D Ω v v ≤ ‖v‖ ^ 2 := by
  rw [gradientEnergy_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  exact sub_le_self _ (sq_nonneg _)

def HasTestPoincare (D : LeviCivitaData g) (Ω : Set M) (P : ℝ) : Prop :=
  ∀ f : EnergyTest D Ω, ‖testToL2 D Ω f‖ ^ 2 ≤
    P * ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure

theorem norm_toL2_sq_le_gradientEnergy {P : ℝ} (hP : HasTestPoincare D Ω P)
    (v : H1Zero D Ω) :
    ‖toL2 D Ω v‖ ^ 2 ≤ P * gradientEnergy D Ω v v := by
  induction v using Completion.induction_on with
  | hp =>
    apply isClosed_le
    · fun_prop
    · fun_prop
  | ih f => simpa only [toL2_coe, gradientEnergy_coe] using hP f

theorem norm_sq_le_gradientEnergy {P : ℝ} (hP : HasTestPoincare D Ω P)
    (v : H1Zero D Ω) :
    ‖v‖ ^ 2 ≤ (P + 1) * gradientEnergy D Ω v v := by
  have h := norm_toL2_sq_le_gradientEnergy hP v
  have he : ‖v‖ ^ 2 = gradientEnergy D Ω v v + ‖toL2 D Ω v‖ ^ 2 := by
    rw [gradientEnergy_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  nlinarith

theorem gradientEnergy_isCoercive {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) : IsCoercive (gradientEnergy D Ω) := by
  refine ⟨(P + 1)⁻¹, by positivity, fun v ↦ ?_⟩
  have hp : 0 < P + 1 := by positivity
  have h := norm_sq_le_gradientEnergy hP v
  calc
    (P + 1)⁻¹ * ‖v‖ * ‖v‖ = ‖v‖ ^ 2 / (P + 1) := by ring
    _ ≤ gradientEnergy D Ω v v := (div_le_iff₀ hp).mpr (by simpa [mul_comm] using h)

def weakDirichlet (D : LeviCivitaData g) (Ω : Set M) {P : ℝ}
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P) :
    (H1Zero D Ω →L[ℝ] ℝ) →L[ℝ] H1Zero D Ω :=
  (gradientEnergy_isCoercive hP0 hP).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ (H1Zero D Ω)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem weakDirichlet_spec {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P)
    (ell : H1Zero D Ω →L[ℝ] ℝ) (v : H1Zero D Ω) :
    gradientEnergy D Ω (weakDirichlet D Ω hP0 hP ell) v = ell v := by
  rw [← (gradientEnergy_isCoercive hP0 hP).continuousLinearEquivOfBilin_apply]
  simp only [weakDirichlet, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

theorem weakDirichlet_unique {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P)
    (ell : H1Zero D Ω →L[ℝ] ℝ) (w : H1Zero D Ω)
    (hw : ∀ v : H1Zero D Ω, gradientEnergy D Ω w v = ell v) :
    w = weakDirichlet D Ω hP0 hP ell := by
  apply (gradientEnergy_isCoercive hP0 hP).continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [(gradientEnergy_isCoercive hP0 hP).continuousLinearEquivOfBilin_apply,
    (gradientEnergy_isCoercive hP0 hP).continuousLinearEquivOfBilin_apply,
    hw, weakDirichlet_spec]

theorem existsUnique_weakDirichlet {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) (ell : H1Zero D Ω →L[ℝ] ℝ) :
    ∃! w : H1Zero D Ω, ∀ v : H1Zero D Ω, gradientEnergy D Ω w v = ell v := by
  exact ⟨weakDirichlet D Ω hP0 hP ell, weakDirichlet_spec hP0 hP ell,
    fun w hw ↦ weakDirichlet_unique hP0 hP ell w hw⟩

theorem weakDirichlet_unique_of_test {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) (ell : H1Zero D Ω →L[ℝ] ℝ) (w : H1Zero D Ω)
    (hw : ∀ f : EnergyTest D Ω, gradientEnergy D Ω w (f : H1Zero D Ω) = ell f) :
    w = weakDirichlet D Ω hP0 hP ell := by
  apply weakDirichlet_unique hP0 hP ell w
  intro v
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq ((gradientEnergy D Ω) w).continuous ell.continuous
  | ih f => exact hw f

theorem norm_weakDirichlet_apply_le {P : ℝ} (hP0 : 0 ≤ P)
    (hP : HasTestPoincare D Ω P) (ell : H1Zero D Ω →L[ℝ] ℝ) :
    ‖weakDirichlet D Ω hP0 hP ell‖ ≤ (P + 1) * ‖ell‖ := by
  let w := weakDirichlet D Ω hP0 hP ell
  have hp : 0 ≤ P + 1 := by positivity
  have h := norm_sq_le_gradientEnergy hP w
  rw [weakDirichlet_spec] at h
  have hb := mul_le_mul_of_nonneg_left ((le_abs_self (ell w)).trans (ell.le_opNorm w)) hp
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ _
    rw [hw]
    positivity
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    change ‖w‖ ≤ _
    nlinarith

theorem norm_weakDirichlet_le {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P) :
    ‖weakDirichlet D Ω hP0 hP‖ ≤ P + 1 :=
  (weakDirichlet D Ω hP0 hP).opNorm_le_bound (by positivity)
    (norm_weakDirichlet_apply_le hP0 hP)

end PoincareConjecture.LeviCivitaData.Dirichlet
