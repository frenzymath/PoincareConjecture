import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnPhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleGreenIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "a" => curvePeriod / 2
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private theorem halfTurn_step_vertical_green (D : ℝ)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, fderiv ℝ phi p e1 * (if p 0 < a then 0 else D)) =
      ∫ x in I, phi (annulusPoint x 1) * (if x < a then 0 else D) -
        phi (annulusPoint x 0) * (if x < a then 0 else D) := by
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have h := m64HalfTurnPiece_vertical_green
    (u := fun _ : LoopPlane => D) (V := fun _ : LoopPlane => 0)
    (integrable_const D) (integrable_const 0)
    (c0 := fun _ : ℝ => D) (c1 := fun _ : ℝ => D)
    (integrable_const D) (integrable_const D)
    (fun psi hpsi => by
      simpa using m64Annulus_vertical_green_identity
        (contDiff_const : ContDiff ℝ 1 (fun _ : LoopPlane => D)) hpsi)
    (f := fun _ : LoopPlane => 0) (g := phi) contDiff_const hp
  simpa only [smul_eq_mul, mul_zero, integral_zero, zero_add,
    m64HalfTurnPiece, fderiv_const_apply, zero_apply,
    annulusPoint, Matrix.cons_val_zero, ite_mul, mul_ite, zero_mul] using h

theorem m64FreePhaseHalfTurn_vertical_weak
    {u V : LoopPlane → ℝ} {D : ℝ}
    {c0 c1 : ℝ → ℝ} (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V p) +
          (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * c1 x -
          phi (annulusPoint x 0) * c0 x) :
    HasWeakPartialDeriv 1 (fun p => V (m64AnnulusHalfTurn p))
      (m64FreePhaseHalfTurn u D) S := by
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hUi : Integrable u mu := hu.integrable (by norm_num)
  have hVi : Integrable V mu := hV.integrable (by norm_num)
  have hstepLp : MemLp (fun p : LoopPlane =>
      if p 0 < a then (0 : ℝ) else D) 2 mu := by
    convert (m64FreePhaseHalfTurn_memLp (u := fun _ : LoopPlane => 0)
      (memLp_const (0 : ℝ)) D) using 1
    funext p
    simp [m64FreePhaseHalfTurn]
  intro phi hphi hc hs
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by simp)
  have hdp : MemLp (fun p : LoopPlane => fderiv ℝ phi p e1) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
  have htop (x : ℝ) : phi (annulusPoint x 1) = 0 := by
    have hnot : annulusPoint x 1 ∉ S := by
      intro hp
      exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp hp).2.2.2
    exact image_eq_zero_of_notMem_tsupport (fun hp => hnot (hs hp))
  have hbot (x : ℝ) : phi (annulusPoint x 0) = 0 := by
    have hnot : annulusPoint x 0 ∉ S := by
      intro hp
      exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp hp).2.2.1
    exact image_eq_zero_of_notMem_tsupport (fun hp => hnot (hs hp))
  have hgreen' : ∀ psi : LoopPlane → ℝ, ContDiff ℝ 1 psi →
      (∫ p in S, psi p • V p) +
          (∫ p in S, fderiv ℝ psi p e1 • u p) =
        ∫ x in I, psi (annulusPoint x 1) • c1 x -
          psi (annulusPoint x 0) • c0 x := by
    intro psi hpsi
    simpa only [smul_eq_mul] using hgreen psi hpsi
  have hturn := m64HalfTurn_vertical_green hUi hVi hc0 hc1 hgreen' hphi1
  have hturn_zero :
      (∫ p in S, phi p * V (m64AnnulusHalfTurn p)) +
          (∫ p in S, fderiv ℝ phi p e1 * u (m64AnnulusHalfTurn p)) = 0 := by
    simpa only [smul_eq_mul, htop, hbot, zero_mul, integral_zero, sub_self] using hturn
  have hstep := halfTurn_step_vertical_green D hphi1
  have hstep_zero' :
      (∫ p in S, fderiv ℝ phi p e1 *
          (if p 0 < a then (0 : ℝ) else D)) = 0 := by
    simpa only [htop, hbot, zero_mul, integral_zero, sub_self] using hstep
  have hstep_zero :
      (∫ p in S, (if p 0 < a then (0 : ℝ) else D) *
          fderiv ℝ phi p e1) = 0 := by
    simpa only [mul_comm] using hstep_zero'
  have hUT : MemLp (fun p : LoopPlane => u (m64AnnulusHalfTurn p)) 2 mu := by
    simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hu
  have hUTi : Integrable
      (fun p : LoopPlane => u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) mu := by
    have h := hUT.integrable_mul hdp
    change Integrable
      (fun p : LoopPlane => u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) mu at h
    exact h
  have hstepi : Integrable
      (fun p : LoopPlane => (if p 0 < a then (0 : ℝ) else D) *
        fderiv ℝ phi p e1) mu := by
    have h := hstepLp.integrable_mul hdp
    change Integrable
      (fun p : LoopPlane => (if p 0 < a then (0 : ℝ) else D) *
        fderiv ℝ phi p e1) mu at h
    exact h
  have heq (p : LoopPlane) :
      m64FreePhaseHalfTurn u D p =
        u (m64AnnulusHalfTurn p) +
          (if p 0 < a then (0 : ℝ) else D) := by
    by_cases hp : p 0 < a <;> simp [m64FreePhaseHalfTurn, hp]
  have hsplit :
      (∫ p in S, m64FreePhaseHalfTurn u D p * fderiv ℝ phi p e1) =
        (∫ p in S, u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) +
          ∫ p in S, (if p 0 < a then (0 : ℝ) else D) *
            fderiv ℝ phi p e1 := by
    rw [← integral_add hUTi hstepi]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [heq]
    ring
  have hbase :
      (∫ p in S, u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) =
        -(∫ p in S, V (m64AnnulusHalfTurn p) * phi p) := by
    have h' :
        (∫ p in S, fderiv ℝ phi p e1 * u (m64AnnulusHalfTurn p)) +
            (∫ p in S, phi p * V (m64AnnulusHalfTurn p)) = 0 := by
      linarith [hturn_zero]
    simpa only [mul_comm] using (eq_neg_iff_add_eq_zero.mpr h')
  rw [hsplit, hstep_zero, add_zero, hbase]

theorem m64FreePhaseHalfTurn_vertical_green_split
    {u V : LoopPlane → ℝ} {D : ℝ}
    {c0 c1 : ℝ → ℝ} (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V p) +
          (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * c1 x -
          phi (annulusPoint x 0) * c0 x)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * V (m64AnnulusHalfTurn p)) +
        (∫ p in S, fderiv ℝ phi p e1 * m64FreePhaseHalfTurn u D p) =
      (∫ x in I, phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
          phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x)) +
        ∫ x in I,
          phi (annulusPoint x 1) * (if x < a then 0 else D) -
            phi (annulusPoint x 0) * (if x < a then 0 else D) := by
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hUi : Integrable u mu := hu.integrable (by norm_num)
  have hVi : Integrable V mu := hV.integrable (by norm_num)
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by simp)
  have hdp : MemLp (fun p : LoopPlane => fderiv ℝ phi p e1) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hturn := m64HalfTurn_vertical_green hUi hVi hc0 hc1
    (fun psi hpsi => by
      simpa only [smul_eq_mul] using hgreen psi hpsi) hphi1
  have hstep := halfTurn_step_vertical_green D hphi1
  have hUT : MemLp (fun p : LoopPlane => u (m64AnnulusHalfTurn p)) 2 mu := by
    simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hu
  have hstepLp : MemLp (fun p : LoopPlane =>
      if p 0 < a then (0 : ℝ) else D) 2 mu := by
    convert (m64FreePhaseHalfTurn_memLp (u := fun _ : LoopPlane => 0)
      (memLp_const (0 : ℝ)) D) using 1
    funext p
    simp [m64FreePhaseHalfTurn]
  have hUTi : Integrable
      (fun p => u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) mu := by
    have h := hUT.integrable_mul hdp
    change Integrable
      (fun p => u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) mu at h
    exact h
  have hstepi : Integrable
      (fun p => (if p 0 < a then (0 : ℝ) else D) *
        fderiv ℝ phi p e1) mu := by
    have h := hstepLp.integrable_mul hdp
    change Integrable
      (fun p => (if p 0 < a then (0 : ℝ) else D) *
        fderiv ℝ phi p e1) mu at h
    exact h
  have heq (p : LoopPlane) :
      m64FreePhaseHalfTurn u D p =
        u (m64AnnulusHalfTurn p) +
          (if p 0 < a then (0 : ℝ) else D) := by
    by_cases hp : p 0 < a <;> simp [m64FreePhaseHalfTurn, hp]
  have hsplit :
      (∫ p in S, fderiv ℝ phi p e1 * m64FreePhaseHalfTurn u D p) =
        (∫ p in S, u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) +
          ∫ p in S, (if p 0 < a then (0 : ℝ) else D) *
            fderiv ℝ phi p e1 := by
    rw [← integral_add hUTi hstepi]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [heq]
    ring
  have hUTcomm :
      (∫ p in S, u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) =
        ∫ p in S, fderiv ℝ phi p e1 * u (m64AnnulusHalfTurn p) := by
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  have hstepcomm :
      (∫ p in S, (if p 0 < a then (0 : ℝ) else D) *
          fderiv ℝ phi p e1) =
        ∫ p in S, fderiv ℝ phi p e1 *
          (if p 0 < a then (0 : ℝ) else D) := by
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  have hturn' :
      (∫ p in S, phi p * V (m64AnnulusHalfTurn p)) +
          (∫ p in S, fderiv ℝ phi p e1 * u (m64AnnulusHalfTurn p)) =
        ∫ x in I, phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
          phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x) := by
    simpa only [smul_eq_mul] using hturn
  calc
    _ = (∫ p in S, phi p * V (m64AnnulusHalfTurn p)) +
        ((∫ p in S, u (m64AnnulusHalfTurn p) * fderiv ℝ phi p e1) +
          ∫ p in S, (if p 0 < a then (0 : ℝ) else D) *
            fderiv ℝ phi p e1) := by rw [hsplit]
    _ = ((∫ p in S, phi p * V (m64AnnulusHalfTurn p)) +
          ∫ p in S, fderiv ℝ phi p e1 * u (m64AnnulusHalfTurn p)) +
        ∫ p in S, fderiv ℝ phi p e1 *
          (if p 0 < a then (0 : ℝ) else D) := by
      rw [hUTcomm, hstepcomm]
      ring
    _ = (∫ x in I, phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
          phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x)) +
        ∫ p in S, fderiv ℝ phi p e1 *
          (if p 0 < a then (0 : ℝ) else D) := by rw [hturn']
    _ = (∫ x in I, phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
          phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x)) +
        ∫ x in I,
          phi (annulusPoint x 1) * (if x < a then 0 else D) -
            phi (annulusPoint x 0) * (if x < a then 0 else D) := by rw [hstep]

theorem m64FreePhaseHalfTurn_vertical_green_with_jump
    {u V : LoopPlane → ℝ} {D : ℝ}
    {c0 c1 : ℝ → ℝ} (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V p) +
          (∫ p in S, fderiv ℝ phi p e1 * u p) =
        ∫ x in I, phi (annulusPoint x 1) * c1 x -
          phi (annulusPoint x 0) * c0 x)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * V (m64AnnulusHalfTurn p)) +
        (∫ p in S, fderiv ℝ phi p e1 * m64FreePhaseHalfTurn u D p) =
      ∫ x in I,
        phi (annulusPoint x 1) *
            (c1 (m64BoundaryHalfTurn x) + (if x < a then 0 else D)) -
          phi (annulusPoint x 0) *
            (c0 (m64BoundaryHalfTurn x) + (if x < a then 0 else D)) := by
  have hsplit := m64FreePhaseHalfTurn_vertical_green_split (D := D)
    hu hV hc0 hc1 hgreen hphi
  have htrans (c : ℝ → ℝ) (hc : Continuous c) (s : ℝ) :
      IntegrableOn
        (fun x => phi (annulusPoint x s) * c (m64BoundaryHalfTurn x)) I volume := by
    have hci : Integrable c (volume.restrict I) := hc.integrableOn_Icc
    have hcm := m64BoundaryHalfTurn_measurePreserving.integrable_comp_of_integrable hci
    have hpC := hphi.continuous.comp (m64Source_annulusPoint_contDiff s).continuous
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact I).exists_bound_of_continuousOn hpC.continuousOn
    have hh := hcm.bdd_smul C hpC.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hC x hx)
    change Integrable
      (fun x => phi (annulusPoint x s) * c (m64BoundaryHalfTurn x))
      (volume.restrict I)
    convert hh using 1
    ext x
    rfl
  have hstep (s : ℝ) :
      IntegrableOn
        (fun x => phi (annulusPoint x s) * (if x < a then (0 : ℝ) else D)) I volume := by
    let muI := volume.restrict I
    have hpC : Continuous (fun x => phi (annulusPoint x s)) :=
      hphi.continuous.comp (m64Source_annulusPoint_contDiff s).continuous
    have hphiI : Integrable (fun x => phi (annulusPoint x s)) muI :=
      hpC.integrableOn_Icc
    have hprodI : Integrable
        (fun x => phi (annulusPoint x s) * D) muI := hphiI.mul_const D
    have hpiece : Integrable ((Set.Iio a).piecewise
        (fun _ : ℝ => (0 : ℝ))
          (fun x => phi (annulusPoint x s) * D)) muI := by
      have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Iio a) muI := by
        change Integrable (fun _ : ℝ => (0 : ℝ)) (muI.restrict (Set.Iio a))
        exact integrable_zero ℝ ℝ (muI.restrict (Set.Iio a))
      apply Integrable.piecewise measurableSet_Iio hzero
      exact hprodI.mono_measure (Measure.restrict_le_self)
    have heq :
        ((Set.Iio a).piecewise (fun _ : ℝ => (0 : ℝ))
          (fun x => phi (annulusPoint x s) * D)) =ᵐ[muI]
        (fun x => phi (annulusPoint x s) * (if x < a then (0 : ℝ) else D)) := by
      filter_upwards [] with x
      by_cases hx : x < a <;> simp [Set.piecewise, hx]
    exact hpiece.congr heq
  have htrans' : IntegrableOn
      (fun x => phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
        phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x)) I volume :=
    (htrans c1 hc1 1).sub (htrans c0 hc0 0)
  have hstep' : IntegrableOn
      (fun x => phi (annulusPoint x 1) * (if x < a then (0 : ℝ) else D) -
        phi (annulusPoint x 0) * (if x < a then (0 : ℝ) else D)) I volume :=
    (hstep 1).sub (hstep 0)
  calc
    _ = (∫ x in I, phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
          phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x)) +
        ∫ x in I,
          phi (annulusPoint x 1) * (if x < a then 0 else D) -
            phi (annulusPoint x 0) * (if x < a then 0 else D) := hsplit
    _ = ∫ x in I,
        (phi (annulusPoint x 1) * c1 (m64BoundaryHalfTurn x) -
            phi (annulusPoint x 0) * c0 (m64BoundaryHalfTurn x)) +
          (phi (annulusPoint x 1) * (if x < a then 0 else D) -
            phi (annulusPoint x 0) * (if x < a then 0 else D)) := by
      rw [integral_add htrans' hstep']
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

end PoincareConjecture
