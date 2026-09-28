import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnPhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleGreenIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicGreenIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "T" => m64AnnulusHalfTurn
local notation "a" => curvePeriod / 2
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

private theorem m64_seam_coordinate_memLp :
    MemLp (fun p : LoopPlane => p 0) 2 mu := by
  apply m64Annulus_continuous_memLp_two
  exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous

private theorem m64_seam_coordinate_fderiv (p : LoopPlane) :
    fderiv ℝ (fun q : LoopPlane => q 0) p e0 = 1 := by
  have hd : fderiv ℝ (fun q : LoopPlane => q 0) p =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) : LoopPlane →L[ℝ] ℝ) :=
    (show LoopPlane →L[ℝ] ℝ from EuclideanSpace.proj 0).fderiv
  rw [hd]
  change (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) e0 = 1
  change (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 = 1
  rfl

private theorem m64_free_phase_halfTurn_horizontal_zero
    {u V : LoopPlane → ℝ} {D : ℝ}
    (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V p) +
        (∫ p in S, fderiv ℝ phi p e0 * u p) =
          D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * (V p - D / curvePeriod)) +
        (∫ p in S, fderiv ℝ phi p e0 *
          (u p - (D / curvePeriod) * p 0)) = 0 := by
  intro phi hphi hperiod
  let q : ℝ := D / curvePeriod
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hP : curvePeriod ≠ 0 := by
    unfold curvePeriod
    norm_num
  have hcoordf : ContDiff ℝ 1 (fun p : LoopPlane => p 0) := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞)).of_le (by simp)
  have hcoord := m64Annulus_horizontal_green_identity
    (f := fun p : LoopPlane => p 0) (phi := phi) hcoordf hphi
  have hcoord' :
      (∫ p in S, phi p * (1 : ℝ)) +
        (∫ p in S, fderiv ℝ phi p e0 * p 0) =
          curvePeriod * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
    simp only [m64_seam_coordinate_fderiv] at hcoord
    have hright :
        (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) *
          curvePeriod) =
          curvePeriod * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with s
      ring
    calc
      _ = ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) *
          curvePeriod := by
        simpa [smul_eq_mul, annulusPoint] using hcoord
      _ = _ := hright
  have hphiLp : MemLp phi 2 mu := m64Annulus_continuous_memLp_two hphi.continuous
  have hdphiLp : MemLp (fun p => fderiv ℝ phi p e0) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hVint : Integrable (fun p => phi p * V p) mu := by
    have h := hV.integrable_mul hphiLp
    change Integrable (fun p => V p * phi p) mu at h
    simpa only [mul_comm] using h
  have hqphi : Integrable (fun p => phi p * q) mu := by
    have hi : Integrable phi mu := hphiLp.integrable (by norm_num)
    simpa only [Pi.mul_apply, mul_comm] using hi.const_mul q
  have huint : Integrable (fun p => fderiv ℝ phi p e0 * u p) mu := by
    have h := hu.integrable_mul hdphiLp
    change Integrable (fun p => u p * fderiv ℝ phi p e0) mu at h
    simpa only [mul_comm] using h
  have hqcoord : Integrable
      (fun p => fderiv ℝ phi p e0 * (q * p 0)) mu := by
    have h := (m64_seam_coordinate_memLp.integrable_mul hdphiLp).const_mul q
    change Integrable (fun p => q * (p 0 * fderiv ℝ phi p e0)) mu at h
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hq := hseam phi hphi hperiod
  have hqcoord' :
      (∫ p in S, phi p * q) +
        (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) =
          D * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
    have hfirst : (∫ p in S, phi p * q) = q * ∫ p in S, phi p := by
      calc
        _ = ∫ p in S, q * phi p := by
          apply integral_congr_ae
          filter_upwards [] with p
          ring
        _ = _ := by rw [integral_const_mul]
    have hsecond :
        (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) =
          q * ∫ p in S, fderiv ℝ phi p e0 * p 0 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    have hbase :
        (∫ p in S, phi p) +
            ∫ p in S, fderiv ℝ phi p e0 * p 0 =
          curvePeriod * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
      simpa only [mul_one] using hcoord'
    rw [hfirst, hsecond]
    have hqbase := congrArg (fun z : ℝ => q * z) hbase
    rw [mul_add] at hqbase
    rw [hqbase]
    dsimp [q]
    field_simp [hP]
  change (∫ p in S, phi p * (V p - q)) +
      (∫ p in S, fderiv ℝ phi p e0 * (u p - q * p 0)) = 0
  have hsplitV :
      (∫ p in S, phi p * (V p - q)) =
        (∫ p in S, phi p * V p) - ∫ p in S, phi p * q := by
    calc
      _ = ∫ p in S, (phi p * V p - phi p * q) := by
        apply integral_congr_ae
        filter_upwards [] with p
        ring
      _ = _ := by
        simpa only [mul_comm] using integral_sub hVint hqphi
  have hsplitU :
      (∫ p in S, fderiv ℝ phi p e0 * (u p - q * p 0)) =
        (∫ p in S, fderiv ℝ phi p e0 * u p) -
          ∫ p in S, fderiv ℝ phi p e0 * (q * p 0) := by
    calc
      _ = ∫ p in S,
          (fderiv ℝ phi p e0 * u p -
            fderiv ℝ phi p e0 * (q * p 0)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        ring
      _ = _ := by exact integral_sub huint hqcoord
  rw [hsplitV, hsplitU]
  linarith [hq, hqcoord']

theorem m64FreePhaseHalfTurn_seam_green
    {u V : LoopPlane → ℝ} {D : ℝ}
    (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V p) +
        (∫ p in S, fderiv ℝ phi p e0 * u p) =
          D * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s)) :
    ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V (T p)) +
        (∫ p in S, fderiv ℝ phi p e0 * m64FreePhaseHalfTurn u D p) =
          D * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
  let q : ℝ := D / curvePeriod
  let w : LoopPlane → ℝ := fun p => u p - q * p 0
  let W : LoopPlane → ℝ := fun p => V p - q
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hw : MemLp w 2 mu := by
    exact hu.sub (m64_seam_coordinate_memLp.const_mul q)
  have hW : MemLp W 2 mu := by
    exact hV.sub (memLp_const q)
  have hzero := m64_free_phase_halfTurn_horizontal_zero hu hV hseam
  intro phi hphi hperiod
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by simp)
  have hphiLp : MemLp phi 2 mu := m64Annulus_continuous_memLp_two hphi.continuous
  have hdphiLp : MemLp (fun p => fderiv ℝ phi p e0) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hwi : Integrable w mu := hw.integrable (by norm_num)
  have hWi : Integrable W mu := hW.integrable (by norm_num)
  have hturn := m64HalfTurn_seam_green hwi hWi
    (fun psi hpsi hpsi_seam => by
      simpa only [smul_eq_mul] using hzero psi hpsi hpsi_seam)
    hphi1 hperiod
  have hWT : MemLp (fun p : LoopPlane => w (T p)) 2 mu := by
    simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hw
  have hWT' : MemLp (fun p : LoopPlane => W (T p)) 2 mu := by
    simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hW
  have heq : (fun p => m64FreePhaseHalfTurn u D p) =ᵐ[mu]
      (fun p => w (T p) + q * p 0 + q * a) := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet,
      ae_restrict_of_ae m64AnnulusHalf_ae_union] with p hp hparts
    rcases hparts.mp hp with hleft | hright
    · have hT : T p = p + annulusPoint a 0 := by
        simp only [m64AnnulusHalfTurn, if_pos hleft.2.1]
      simp only [m64FreePhaseHalfTurn, if_pos hleft.2.1, w, q]
      rw [hT]
      simp only [PiLp.add_apply, annulusPoint, Matrix.cons_val_zero]
      ring
    · have hT : T p = p - annulusPoint a 0 := by
        simp only [m64AnnulusHalfTurn, if_neg (not_lt.mpr hright.1.le)]
      simp only [m64FreePhaseHalfTurn, if_neg (not_lt.mpr hright.1.le), w, q]
      rw [hT]
      simp only [PiLp.sub_apply, annulusPoint, Matrix.cons_val_zero]
      have hP : curvePeriod ≠ 0 := by
        unfold curvePeriod
        norm_num
      field_simp [hP]
      ring
  have hcoordf : ContDiff ℝ 1 (fun p : LoopPlane => p 0) := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞)).of_le (by simp)
  have hcoord := m64Annulus_horizontal_green_identity
    (f := fun p : LoopPlane => p 0) (phi := phi) hcoordf hphi1
  have hcoord' :
      (∫ p in S, phi p * (1 : ℝ)) +
        (∫ p in S, fderiv ℝ phi p e0 * p 0) =
          curvePeriod * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
    simp only [m64_seam_coordinate_fderiv] at hcoord
    have hright :
        (∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) *
          curvePeriod) =
          curvePeriod * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with s
      ring
    calc
      _ = ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) *
          curvePeriod := by
        simpa [smul_eq_mul, annulusPoint] using hcoord
      _ = _ := hright
  have hdzero :
      (∫ p in S, fderiv ℝ phi p e0) = 0 := by
    have h := m64Annulus_horizontal_green_identity
      (f := fun _ : LoopPlane => (1 : ℝ)) (phi := phi)
      (contDiff_const : ContDiff ℝ 1 (fun _ : LoopPlane => (1 : ℝ))) hphi1
    have hright :
        (∫ s in Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) * (1 : ℝ) -
            phi (annulusPoint 0 s) * (1 : ℝ)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      change phi (annulusPoint curvePeriod s) * (1 : ℝ) -
        phi (annulusPoint 0 s) * (1 : ℝ) = (0 : ℝ)
      rw [hperiod s hs]
      ring
    have hright' :
        (∫ s in Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) • (1 : ℝ) -
            phi (annulusPoint 0 s) • (1 : ℝ)) = 0 := by
      simpa only [smul_eq_mul] using hright
    rw [hright'] at h
    simpa only [fderiv_const_apply, zero_apply, zero_mul, mul_zero, integral_zero,
      zero_add, add_zero, mul_one, smul_eq_mul] using h
  have hWphi : Integrable
      (fun p => phi p * W (T p)) mu := by
    have h := hWT'.integrable_mul hphiLp
    change Integrable (fun p => W (T p) * phi p) mu at h
    simpa only [mul_comm] using h
  have hqphi : Integrable (fun p => phi p * q) mu := by
    have h := hphiLp.integrable (by norm_num)
    simpa only [Pi.mul_apply, mul_comm] using h.const_mul q
  have hWsplit :
      (∫ p in S, phi p * V (T p)) =
        (∫ p in S, phi p * W (T p)) + q * ∫ p in S, phi p := by
    have hqphi_eq :
        (∫ p in S, phi p * q) = q * ∫ p in S, phi p := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    rw [← hqphi_eq, ← integral_add hWphi hqphi]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [W]
    ring
  have hWTd : Integrable
      (fun p => fderiv ℝ phi p e0 * w (T p)) mu := by
    have h := hWT.integrable_mul hdphiLp
    change Integrable (fun p => w (T p) * fderiv ℝ phi p e0) mu at h
    simpa only [mul_comm] using h
  have hcoordd : Integrable
      (fun p => fderiv ℝ phi p e0 * (q * p 0)) mu := by
    have h := m64_seam_coordinate_memLp.integrable_mul hdphiLp |>.const_mul q
    change Integrable (fun p => q * (p 0 * fderiv ℝ phi p e0)) mu at h
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hconstd : Integrable
      (fun p => fderiv ℝ phi p e0 * (q * a)) mu := by
    have h := (memLp_const (q * a) : MemLp (fun _ : LoopPlane => q * a) 2 mu)
      |>.integrable_mul hdphiLp
    change Integrable (fun p => (q * a) * fderiv ℝ phi p e0) mu at h
    simpa only [mul_comm] using h
  have hfree_split :
      (∫ p in S, fderiv ℝ phi p e0 * m64FreePhaseHalfTurn u D p) =
        (∫ p in S, fderiv ℝ phi p e0 * w (T p)) +
          (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) +
          (∫ p in S, fderiv ℝ phi p e0 * (q * a)) := by
    calc
      _ = ∫ p in S,
          ((fderiv ℝ phi p e0 * w (T p) +
            fderiv ℝ phi p e0 * (q * p 0)) +
            fderiv ℝ phi p e0 * (q * a)) := by
        apply integral_congr_ae
        filter_upwards [heq] with p hp
        rw [hp]
        ring
      _ = (∫ p in S,
          (fderiv ℝ phi p e0 * w (T p) +
            fderiv ℝ phi p e0 * (q * p 0))) +
            (∫ p in S, fderiv ℝ phi p e0 * (q * a)) := by
        exact integral_add (hWTd.add hcoordd) hconstd
      _ = ((∫ p in S, fderiv ℝ phi p e0 * w (T p)) +
            (∫ p in S, fderiv ℝ phi p e0 * (q * p 0))) +
            (∫ p in S, fderiv ℝ phi p e0 * (q * a)) := by
        rw [integral_add hWTd hcoordd]
  have hcoordscale :
      (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) =
        q * ∫ p in S, fderiv ℝ phi p e0 * p 0 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  have hconstzero :
      (∫ p in S, fderiv ℝ phi p e0 * (q * a)) = 0 := by
    have hscale :
        (∫ p in S, fderiv ℝ phi p e0 * (q * a)) =
          (q * a) * ∫ p in S, fderiv ℝ phi p e0 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    rw [hscale, hdzero, mul_zero]
  have hturn' :
      (∫ p in S, phi p * W (T p)) +
          ∫ p in S, fderiv ℝ phi p e0 * w (T p) = 0 := by
    simpa only [smul_eq_mul] using hturn
  have hcoord_main :
      (∫ p in S, phi p) +
          ∫ p in S, fderiv ℝ phi p e0 * p 0 =
        curvePeriod * ∫ s in Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) := by
    simpa only [mul_one] using hcoord'
  have hmain :
      ((∫ p in S, phi p * W (T p)) + q * (∫ p in S, phi p)) +
          ((∫ p in S, fderiv ℝ phi p e0 * w (T p)) +
            (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) +
            (∫ p in S, fderiv ℝ phi p e0 * (q * a))) =
        q * ((∫ p in S, phi p) +
          (∫ p in S, fderiv ℝ phi p e0 * p 0)) := by
    rw [hcoordscale, hconstzero]
    calc
      _ = ((∫ p in S, phi p * W (T p)) +
            (∫ p in S, fderiv ℝ phi p e0 * w (T p))) +
          q * (∫ p in S, phi p) +
          q * (∫ p in S, fderiv ℝ phi p e0 * p 0) := by ring
      _ = _ := by rw [hturn']; ring
  calc
    _ = (∫ p in S, phi p * W (T p)) + q * (∫ p in S, phi p) +
        ((∫ p in S, fderiv ℝ phi p e0 * w (T p)) +
          (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) +
          (∫ p in S, fderiv ℝ phi p e0 * (q * a))) := by
      rw [hWsplit, hfree_split]
    _ = q * ((∫ p in S, phi p) +
          (∫ p in S, fderiv ℝ phi p e0 * p 0)) := by
      exact hmain
    _ = D * ∫ s in Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) := by
      rw [hcoord_main]
      dsimp [q]
      field_simp [show curvePeriod ≠ 0 by unfold curvePeriod; norm_num]

end PoincareConjecture
