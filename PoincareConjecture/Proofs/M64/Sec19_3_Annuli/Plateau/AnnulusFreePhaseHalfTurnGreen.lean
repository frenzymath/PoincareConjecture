import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnPhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicGreenIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "T" => m64AnnulusHalfTurn
local notation "a" => curvePeriod / 2
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private theorem m64_annulus_coordinate_memLp :
    MemLp (fun p : LoopPlane => p 0) 2 mu := by
  apply m64Annulus_continuous_memLp_two
  exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous

private theorem m64_annulus_coordinate_fderiv (p : LoopPlane) :
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
    (f := fun p : LoopPlane => p 0) (phi := phi)
    hcoordf hphi
  have hcoord' :
      (∫ p in S, phi p * (1 : ℝ)) +
        (∫ p in S, fderiv ℝ phi p e0 * p 0) =
          curvePeriod * ∫ s in Icc (0 : ℝ) 1,
            phi (annulusPoint curvePeriod s) := by
    simp only [m64_annulus_coordinate_fderiv] at hcoord
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
  have hphiLp : MemLp phi 2 mu := by
    exact m64Annulus_continuous_memLp_two hphi.continuous
  have hdphiLp : MemLp (fun p => fderiv ℝ phi p e0) 2 mu := by
    exact m64Annulus_continuous_memLp_two
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
  have hqcoord : Integrable (fun p => fderiv ℝ phi p e0 * (q * p 0)) mu := by
    have hc := m64_annulus_coordinate_memLp
    have h := (hc.integrable_mul hdphiLp).const_mul q
    change Integrable (fun p => q * (p 0 * fderiv ℝ phi p e0)) mu at h
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hq := hseam phi hphi hperiod
  have hqcoord' :
      (∫ p in S, phi p * q) +
        (∫ p in S, fderiv ℝ phi p e0 * (q * p 0)) =
          D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) := by
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
        (∫ p in S, phi p) + ∫ p in S, fderiv ℝ phi p e0 * p 0 =
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

theorem m64FreePhaseHalfTurn_horizontal_weak
    {u V : LoopPlane → ℝ} {D : ℝ}
    (hu : MemLp u 2 mu) (hV : MemLp V 2 mu)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V p) +
        (∫ p in S, fderiv ℝ phi p e0 * u p) =
          D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) :
    HasWeakPartialDeriv 0 (fun p => V (T p))
      (m64FreePhaseHalfTurn u D) S := by
  let q : ℝ := D / curvePeriod
  let w : LoopPlane → ℝ := fun p => u p - q * p 0
  let W : LoopPlane → ℝ := fun p => V p - q
  let : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have hw : MemLp w 2 mu := by
    exact hu.sub (m64_annulus_coordinate_memLp.const_mul q)
  have hW : MemLp W 2 mu := by
    exact hV.sub (memLp_const q)
  have hzero := m64_free_phase_halfTurn_horizontal_zero hu hV hseam
  have hturn : HasWeakPartialDeriv 0 (fun p => W (T p)) (fun p => w (T p)) S := by
    intro phi hphi hc hs
    have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by simp)
    have hseam0 : ∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s) := by
      intro s hsI
      have htop : annulusPoint curvePeriod s ∉ S := by
        intro h
        exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp h).2.1
      have hbot : annulusPoint 0 s ∉ S := by
        intro h
        exact lt_irrefl _ ((m64AnnulusInterior_coordinates _).mp h).1
      have ht := image_eq_zero_of_notMem_tsupport (fun hq => htop (hs hq))
      have hb := image_eq_zero_of_notMem_tsupport (fun hq => hbot (hs hq))
      rw [ht, hb]
    have hwi : Integrable w mu := hw.integrable (by norm_num)
    have hWi : Integrable W mu := hW.integrable (by norm_num)
    have ht := m64HalfTurn_seam_green hwi hWi
      (fun psi hpsi hpsi_seam => by
        simpa only [smul_eq_mul] using hzero psi hpsi hpsi_seam)
      hphi1 hseam0
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [smul_eq_mul, mul_comm, add_comm] using ht
  have hcoordweak : HasWeakPartialDeriv 0 (fun _ : LoopPlane => q)
      (fun p : LoopPlane => q * p 0) S := by
    have hcoordf : ContDiff ℝ 1 (fun p : LoopPlane => p 0) := by
      exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
        (n := ∞)).of_le (by simp)
    have h := HasWeakPartialDeriv.of_contDiff (Ω := S) isOpen_interior
      hcoordf (i := 0)
    have hh := m64WeakPartial_const_mul h q
    convert hh using 1
    · funext p
      rw [m64_annulus_coordinate_fderiv]
      ring
  have haff : HasWeakPartialDeriv 0
      (fun p => W (T p) + q) (fun p => w (T p) + q * p 0) S := by
    have hWT : MemLp (fun p => w (T p)) 2 mu := by
      simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hw
    have hWT' : MemLp (fun p => W (T p)) 2 mu := by
      simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hW
    exact m64WeakPartial_add hWT (m64_annulus_coordinate_memLp.const_mul q) hWT'
      (memLp_const q) hturn hcoordweak
  have heq : (fun p => m64FreePhaseHalfTurn u D p) =ᵐ[mu]
      (fun p => w (T p) + q * p 0 + q * a) := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet,
      ae_restrict_of_ae m64AnnulusHalf_ae_union] with p hp hparts
    rcases hparts.mp hp with hleft | hright
    · have hT : m64AnnulusHalfTurn p = p + annulusPoint a 0 := by
        simp only [m64AnnulusHalfTurn, if_pos hleft.2.1]
      simp only [m64FreePhaseHalfTurn, if_pos hleft.2.1, w, q]
      rw [hT]
      simp only [PiLp.add_apply, annulusPoint, Matrix.cons_val_zero]
      ring
    · have hT : m64AnnulusHalfTurn p = p - annulusPoint a 0 := by
        simp only [m64AnnulusHalfTurn, if_neg (not_lt.mpr hright.1.le)]
      simp only [m64FreePhaseHalfTurn, if_neg (not_lt.mpr hright.1.le), w, q]
      rw [hT]
      simp only [PiLp.sub_apply, annulusPoint, Matrix.cons_val_zero]
      have hP : curvePeriod ≠ 0 := by
        unfold curvePeriod
        norm_num
      field_simp [hP]
      ring
  have haff' : HasWeakPartialDeriv 0 (fun p => V (T p))
      (fun p => w (T p) + q * p 0) S := by
    intro phi hphi hc hs
    have hh := haff phi hphi hc hs
    apply eq_neg_iff_add_eq_zero.mpr
    have hi : (∫ p in S, V (T p) * phi p) =
        ∫ p in S, (W (T p) + q) * phi p := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [W]
      ring
    rw [hi]
    have hh' :
        (∫ p in S, (w (T p) + q * p 0) *
          fderiv ℝ phi p e0) +
          ∫ p in S, (W (T p) + q) * phi p = 0 := by
      linarith [hh]
    simpa only [mul_comm, add_comm] using hh'
  intro phi hphi hc hs
  have hh := haff' phi hphi hc hs
  have hdp : MemLp (fun p => fderiv ℝ phi p e0) 2 mu :=
    m64Annulus_continuous_memLp_two
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hbaseLp : MemLp (fun p => w (T p) + q * p 0) 2 mu := by
    have hWT : MemLp (fun p => w (T p)) 2 mu := by
      simpa only [Function.comp_def] using m64AnnulusHalfTurn_memLp hw
    exact hWT.add (m64_annulus_coordinate_memLp.const_mul q)
  have hbaseInt : Integrable
      (fun p => (w (T p) + q * p 0) * fderiv ℝ phi p e0) mu := by
    have h := hbaseLp.integrable_mul hdp
    change Integrable
      (fun p => (w (T p) + q * p 0) * fderiv ℝ phi p e0) mu at h
    exact h
  have hconstInt : Integrable
      (fun p => (q * a) * fderiv ℝ phi p e0) mu := by
    have h := (memLp_const (q * a) : MemLp (fun _ : LoopPlane => q * a) 2 mu)
      |>.integrable_mul hdp
    change Integrable
      (fun p => (q * a) * fderiv ℝ phi p e0) mu at h
    exact h
  have hconst :
      HasWeakPartialDeriv 0 (fun _ : LoopPlane => 0)
        (fun _ : LoopPlane => q * a) S := by
    have h := HasWeakPartialDeriv.of_contDiff (Ω := S) isOpen_interior
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : LoopPlane => q * a)).of_le (by simp))
      (i := 0)
    simpa using h
  have hconst_zero :
      (∫ p in S, (q * a) * fderiv ℝ phi p e0) = 0 := by
    have h := hconst phi hphi hc hs
    simpa using h
  calc
    (∫ p in S, m64FreePhaseHalfTurn u D p *
        fderiv ℝ phi p e0) =
        ∫ p in S, (w (T p) + q * p 0 + q * a) *
          fderiv ℝ phi p e0 := by
      apply integral_congr_ae
      filter_upwards [heq] with p hp
      rw [hp]
    _ = -(∫ p in S, V (T p) * phi p) := by
      calc
        _ = ∫ p in S,
            ((w (T p) + q * p 0) * fderiv ℝ phi p e0 +
              (q * a) * fderiv ℝ phi p e0) := by
          apply integral_congr_ae
          filter_upwards [] with p
          ring
        _ = (∫ p in S, (w (T p) + q * p 0) *
            fderiv ℝ phi p e0) +
              ∫ p in S, (q * a) * fderiv ℝ phi p e0 := by
          rw [integral_add hbaseInt hconstInt]
        _ = _ := by
          rw [hh, hconst_zero]
          simp

end PoincareConjecture
