import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnPhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMeasurableVerticalGreen

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "T" => m64AnnulusHalfTurn
local notation "a" => curvePeriod / 2
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64FreePhaseHalfTurn_vertical_green
    {u V : LoopPlane → ℝ} {b0 b1 : ℝ → ℝ} {D : ℝ}
    (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hb0 : Continuous b0) (hb1 : Continuous b1)
    (hper0 : ∀ x, b0 (x + curvePeriod) = b0 x + D)
    (hper1 : ∀ x, b1 (x + curvePeriod) = b1 x + D)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * b1 x - phi (annulusPoint x 0) * b0 x)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * V (T p)) +
      (∫ p in S, fderiv ℝ phi p e1 * m64FreePhaseHalfTurn u D p) =
        ∫ x in I, phi (annulusPoint x 1) * b1 (x + a) -
          phi (annulusPoint x 0) * b0 (x + a) := by
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  let q : ℝ → ℝ := fun x => if x < a then 0 else D
  have hq : MemLp q 2 (volume.restrict I) := by
    have hqm : Measurable q :=
      Measurable.ite measurableSet_Iio measurable_const measurable_const
    apply MemLp.of_bound hqm.aestronglyMeasurable |D|
    filter_upwards [] with x
    dsimp only [q]
    split_ifs <;> simp only [norm_zero, abs_nonneg, Real.norm_eq_abs, le_refl]
  have hqP : MemLp (fun p : LoopPlane => q (p 0)) 2 mu :=
    hq.comp_measurePreserving m64Annulus_angular_projection_measurePreserving
  have hd : MemLp (fun p : LoopPlane => fderiv ℝ phi p e1) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
  have huT : MemLp (fun p => u (T p)) 2 mu := m64AnnulusHalfTurn_memLp hu
  have hv := m64HalfTurn_vertical_green (hu.integrable (by norm_num))
    (hV.integrable (by norm_num)) hb0 hb1
    (fun psi hpsi => by simpa only [smul_eq_mul] using hgreen psi hpsi) hp
  simp only [smul_eq_mul] at hv
  have hphase (p : LoopPlane) : m64FreePhaseHalfTurn u D p = u (T p) + q (p 0) := by
    simp only [m64FreePhaseHalfTurn, q]
    split_ifs <;> simp
  have htrace {b : ℝ → ℝ} (hb : ∀ x, b (x + curvePeriod) = b x + D) (x : ℝ) :
      b (m64BoundaryHalfTurn x) + q x = b (x + a) := by
    dsimp only [m64BoundaryHalfTurn, q]
    split_ifs with hx
    · simp
    · rw [← hb]
      congr 1
      ring
  have hbd (b : ℝ → ℝ) (hb : Continuous b) (s : ℝ) :
      IntegrableOn (fun x => phi (annulusPoint x s) * b (m64BoundaryHalfTurn x)) I := by
    have hbT := m64BoundaryHalfTurn_measurePreserving.integrable_comp_of_integrable
      hb.integrableOn_Icc
    have hpc : Continuous (fun x => phi (annulusPoint x s)) := by
      apply hp.continuous.comp
      unfold annulusPoint
      fun_prop
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc.continuousOn
    exact hbT.bdd_mul hpc.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  have hqbd (s : ℝ) : IntegrableOn (fun x => phi (annulusPoint x s) * q x) I := by
    have hpc : Continuous (fun x => phi (annulusPoint x s)) := by
      apply hp.continuous.comp
      unfold annulusPoint
      fun_prop
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc.continuousOn
    have hpLp : MemLp (fun x => phi (annulusPoint x s)) 2 (volume.restrict I) :=
      MemLp.of_bound hpc.aestronglyMeasurable C
        (ae_restrict_of_forall_mem measurableSet_Icc hC)
    exact hpLp.integrable_mul hq
  have hdu : Integrable (fun p => fderiv ℝ phi p e1 * u (T p)) mu :=
    hd.integrable_mul huT
  have hdq : Integrable (fun p => fderiv ℝ phi p e1 * q (p 0)) mu :=
    hd.integrable_mul hqP
  have hbdI : IntegrableOn (fun x => phi (annulusPoint x 1) * b1 (m64BoundaryHalfTurn x) -
      phi (annulusPoint x 0) * b0 (m64BoundaryHalfTurn x)) I :=
    (hbd b1 hb1 1).sub (hbd b0 hb0 0)
  have hqI : IntegrableOn (fun x => phi (annulusPoint x 1) * q x -
      phi (annulusPoint x 0) * q x) I := (hqbd 1).sub (hqbd 0)
  simp_rw [hphase, mul_add]
  rw [integral_add hdu hdq, ← add_assoc, hv,
    m64Annulus_measurable_vertical_green hq hp,
    ← integral_add hbdI hqI]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show phi (annulusPoint x 1) * b1 (m64BoundaryHalfTurn x) -
      phi (annulusPoint x 0) * b0 (m64BoundaryHalfTurn x) +
      (phi (annulusPoint x 1) * q x - phi (annulusPoint x 0) * q x) =
      phi (annulusPoint x 1) * (b1 (m64BoundaryHalfTurn x) + q x) -
        phi (annulusPoint x 0) * (b0 (m64BoundaryHalfTurn x) + q x) by ring,
    htrace hper1, htrace hper0]

end PoincareConjecture
