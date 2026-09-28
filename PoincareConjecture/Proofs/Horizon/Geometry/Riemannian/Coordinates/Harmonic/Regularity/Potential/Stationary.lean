import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.Divergence
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Cutoffs
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology BigOperators NNReal

namespace Poincare.Parabolic.Interior

theorem hasCompactSupport_timeCutoff_one : HasCompactSupport (timeCutoff 1) :=
  hasCompactSupport_rescaled_unit_cutoff (by norm_num) 1

private theorem contDiff_deriv_timeCutoff_one : ContDiff ℝ ∞ (deriv (timeCutoff 1)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_timeCutoff 1)).2

section Lift

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def stationaryLift (u : V → F) (p : V × ℝ) : F := timeCutoff 1 p.2 • u p.1

def stationaryForcing (u G : V → F) (p : V × ℝ) : F :=
  deriv (timeCutoff 1) p.2 • u p.1 - timeCutoff 1 p.2 • G p.1

theorem contDiff_stationaryLift {u : V → F} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (stationaryLift u) :=
  ((contDiff_timeCutoff 1).comp contDiff_snd).smul (hu.comp contDiff_fst)

omit [NormedSpace ℝ V] in
private theorem hasCompactSupport_time_smul {a : ℝ → ℝ} {u : V → F}
    (ha : HasCompactSupport a) (hu : HasCompactSupport u) :
    HasCompactSupport (fun p : V × ℝ => a p.2 • u p.1) := by
  apply HasCompactSupport.of_support_subset_isCompact (hu.prod ha)
  intro p hp
  constructor
  · by_contra hx
    exact hp (by simp [image_eq_zero_of_notMem_tsupport hx])
  · by_contra ht
    exact hp (by simp [image_eq_zero_of_notMem_tsupport ht])

omit [NormedSpace ℝ V] in
theorem hasCompactSupport_stationaryLift {u : V → F} (hu : HasCompactSupport u) :
    HasCompactSupport (stationaryLift u) :=
  hasCompactSupport_time_smul hasCompactSupport_timeCutoff_one hu

theorem contDiff_stationaryForcing {u G : V → F}
    (hu : ContDiff ℝ ∞ u) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (stationaryForcing u G) :=
  ((contDiff_deriv_timeCutoff_one.comp contDiff_snd).smul (hu.comp contDiff_fst)).sub
    ((contDiff_timeCutoff 1).comp contDiff_snd |>.smul (hG.comp contDiff_fst))

omit [NormedSpace ℝ V] in
theorem hasCompactSupport_stationaryForcing {u G : V → F}
    (hu : HasCompactSupport u) (hG : HasCompactSupport G) :
    HasCompactSupport (stationaryForcing u G) :=
  (hasCompactSupport_time_smul hasCompactSupport_timeCutoff_one.deriv hu).sub
    (hasCompactSupport_time_smul hasCompactSupport_timeCutoff_one hG)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp]
theorem stationaryLift_zero (u : V → F) (x : V) : stationaryLift u (x, 0) = 0 := by
  simp [stationaryLift, timeCutoff_zero (by norm_num : (0 : ℝ) < 1)]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp]
theorem stationaryLift_one (u : V → F) (x : V) : stationaryLift u (x, 1) = u x := by
  have h := (timeCutoff_eventuallyEq_one (T := 1) (s := 1)
    (by norm_num) (by norm_num) le_rfl).self_of_nhds
  simp [stationaryLift, h]

theorem spatialDerivative_stationaryLift {u : V → F}
    (hu : ContDiff ℝ ∞ u) (x : V) (s : ℝ) :
    spatialDerivative (stationaryLift u) (x, s) = timeCutoff 1 s • fderiv ℝ u x := by
  rw [← fderiv_spatialSlice (contDiff_stationaryLift hu)]
  exact fderiv_const_smul ((hu.differentiable (by simp)) x) (timeCutoff 1 s)

theorem spatialDerivative_spatialDerivative_stationaryLift {u : V → F}
    (hu : ContDiff ℝ ∞ u) (x : V) (s : ℝ) :
    spatialDerivative (spatialDerivative (stationaryLift u)) (x, s) =
      timeCutoff 1 s • fderiv ℝ (fderiv ℝ u) x := by
  rw [← fderiv_spatialSlice (contDiff_spatialDerivative (contDiff_stationaryLift hu))]
  simp only [spatialDerivative_stationaryLift hu]
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  exact fderiv_const_smul ((hdu.differentiable (by simp)) x)
    (timeCutoff 1 s)

theorem timeDerivative_stationaryLift {u : V → F}
    (hu : ContDiff ℝ ∞ u) (x : V) (s : ℝ) :
    timeDerivative (stationaryLift u) (x, s) = deriv (timeCutoff 1) s • u x := by
  have h := hasDerivAt_timeSlice ((contDiff_stationaryLift hu).differentiable (by simp)) x s
  have hd := (((contDiff_timeCutoff 1).differentiable (by simp)) s).hasDerivAt.smul_const (u x)
  exact h.unique hd

omit [NormedSpace ℝ V] in

theorem holderWith_stationaryLift {u : V → F} {K α : ℝ≥0}
    (hu : HolderWith K α u) (s : ℝ) :
    HolderWith K α (fun x => stationaryLift u (x, s)) := by
  have hnorm : ‖timeCutoff 1 s‖₊ ≤ 1 := by
    change ‖timeCutoff 1 s‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (timeCutoff_mem_Icc 1 s).1]
    exact (timeCutoff_mem_Icc 1 s).2
  have h := HolderWith.smul (timeCutoff 1 s) hu
  apply holderOnWith_univ.mp
  exact (h.holderOnWith univ).mono_const
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (show 0 ≤ K from zero_le))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in

theorem exists_stationaryForcing_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u G : V → F) (U B : ℝ), 0 ≤ U → 0 ≤ B →
      (∀ x, ‖u x‖ ≤ U) → (∀ x, ‖G x‖ ≤ B) →
      ∀ p, ‖stationaryForcing u G p‖ ≤ C * U + B := by
  obtain ⟨C, hC⟩ := hasCompactSupport_timeCutoff_one.deriv.exists_bound_of_continuous
    contDiff_deriv_timeCutoff_one.continuous
  refine ⟨max 0 C, le_max_left _ _, fun u G U B hU hB hu hG p => ?_⟩
  have hderiv : ‖deriv (timeCutoff 1) p.2‖ ≤ max 0 C := (hC p.2).trans (le_max_right _ _)
  have hcut : ‖timeCutoff 1 p.2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (timeCutoff_mem_Icc 1 p.2).1]
    exact (timeCutoff_mem_Icc 1 p.2).2
  calc
    _ ≤ ‖deriv (timeCutoff 1) p.2 • u p.1‖ + ‖timeCutoff 1 p.2 • G p.1‖ := norm_sub_le _ _
    _ = ‖deriv (timeCutoff 1) p.2‖ * ‖u p.1‖ + ‖timeCutoff 1 p.2‖ * ‖G p.1‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ max 0 C * U + 1 * B := by
      gcongr
      · exact hu p.1
      · exact hG p.1
    _ = _ := by rw [one_mul]

end Lift

section Residual

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def stationaryEllipticResidual {ι : Type*} [Fintype ι]
    (u : V → F) (Q : ι → V → F) (e : ι → V) (x : V) : F :=
  Kernel.lapEval (fderiv ℝ (fderiv ℝ u) x) - ∑ i, fderiv ℝ (Q i) x (e i)

theorem contDiff_stationaryEllipticResidual {ι : Type*} [Fintype ι]
    {u : V → F} {Q : ι → V → F} (e : ι → V)
    (hu : ContDiff ℝ ∞ u) (hQ : ∀ i, ContDiff ℝ ∞ (Q i)) :
    ContDiff ℝ ∞ (stationaryEllipticResidual u Q e) := by
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hddu : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hdu.fderiv_right (by simp)
  have hdQ (i) : ContDiff ℝ ∞ (fderiv ℝ (Q i)) := (hQ i).fderiv_right (by simp)
  unfold stationaryEllipticResidual
  exact ((Kernel.lapEval (V := V) (F := F)).contDiff.comp hddu).sub
    (ContDiff.sum fun i _ => (hdQ i).clm_apply contDiff_const)

set_option maxHeartbeats 800000 in
theorem hasCompactSupport_stationaryEllipticResidual {ι : Type*} [Fintype ι]
    {u : V → F} {Q : ι → V → F} (e : ι → V)
    (hu : HasCompactSupport u) (hQ : ∀ i, HasCompactSupport (Q i)) :
    HasCompactSupport (stationaryEllipticResidual u Q e) := by
  unfold stationaryEllipticResidual
  have hdu : HasCompactSupport (fderiv ℝ (fderiv ℝ u)) := (hu.fderiv ℝ).fderiv ℝ
  have hdQ (i) : HasCompactSupport (fun x => fderiv ℝ (Q i) x (e i)) :=
    (hQ i).fderiv_apply ℝ (e i)
  have hsum : HasCompactSupport (fun x => ∑ i, fderiv ℝ (Q i) x (e i)) :=
    by
      classical
      induction (Finset.univ : Finset ι) using Finset.induction_on with
      | empty =>
          convert (HasCompactSupport.zero : HasCompactSupport (0 : V → F)) using 1
          ext x
          simp
      | @insert i s hi ih =>
          convert (hdQ i).add ih using 1
          · rfl
          · funext x
            simp [Finset.sum_insert hi]
  apply HasCompactSupport.sub _ hsum
  exact hdu.comp_left (g := Kernel.lapEval (V := V) (F := F)) (map_zero _)

theorem heatResidual_stationaryLift {u : V → F} (hu : ContDiff ℝ ∞ u) (x : V) (s : ℝ) :
    heatResidual (stationaryLift u) (x, s) =
      deriv (timeCutoff 1) s • u x - timeCutoff 1 s • Kernel.lapEval (fderiv ℝ (fderiv ℝ u) x) := by
  simp only [heatResidual, timeDerivative_stationaryLift hu,
    spatialDerivative_spatialDerivative_stationaryLift hu, map_smul]

theorem heatResidual_stationaryLift_eq_forcing_sub_divergence {ι : Type*} [Fintype ι]
    {u : V → F} {Q : ι → V → F} (e : ι → V)
    (hu : ContDiff ℝ ∞ u) (hQ : ∀ i, ContDiff ℝ ∞ (Q i)) (p : V × ℝ) :
    heatResidual (stationaryLift u) p =
      stationaryForcing u (stationaryEllipticResidual u Q e) p -
        ∑ i, spatialDerivative (stationaryLift (Q i)) p (e i) := by
  rcases p with ⟨x, s⟩
  rw [heatResidual_stationaryLift hu]
  simp only [stationaryForcing, stationaryEllipticResidual,
    spatialDerivative_stationaryLift (hQ _), smul_apply, smul_sub, Finset.smul_sum]
  abel

end Residual

end Poincare.Parabolic.Interior
