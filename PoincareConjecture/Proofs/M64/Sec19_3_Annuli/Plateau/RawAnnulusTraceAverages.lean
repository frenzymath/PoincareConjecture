import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "sigma" => volume.restrict (Icc (0 : ℝ) 1)

local instance : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
  ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in



theorem m64Annulus_continuous_smul_integrable {f : LoopPlane → E}
    {c : LoopPlane → ℝ} (hf : Integrable f mu) (hc : Continuous c) :
    Integrable (fun p => c p • f p) mu := by
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn hc.continuousOn
  exact hf.bdd_smul C hc.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC p (interior_subset hp))




theorem m64Annulus_vertical_average_pairing {f : LoopPlane → E}
    {theta : ℝ → ℝ} (hf : Integrable f mu) (htheta : Continuous theta) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
      theta x • ∫ s in Icc (0 : ℝ) 1, f (annulusPoint x s)) =
        ∫ p in S, theta (p 0) • f p := by
  have hc : Continuous (fun p : LoopPlane => theta (p 0)) :=
    htheta.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous
  rw [m64AnnulusInteriorIntegral_eq_iterated_integrable _
    (m64Annulus_continuous_smul_integrable hf hc)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => (integral_smul (theta x) _).symm

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}




theorem M64ObservedWeakAnnulus.radial_green_average
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (h0 : Integrable (e ∘ c0) nu) (h1 : Integrable (e ∘ c1) nu) (a b : ℝ) :
    ∀ᵐ x ∂nu, (∫ s in Icc (0 : ℝ) 1,
      b • e (A.map (annulusPoint x s)) +
        (a + b * s) • A.column 1 (annulusPoint x s)) =
          (a + b) • e (c1 x) - a • e (c0 x) := by
  let f := fun p : LoopPlane => b • e (A.map p) + (a + b * p 1) • A.column 1 p
  have hu : Integrable (fun p => e (A.map p)) mu := A.observed_memLp.integrable (by norm_num)
  have hv : Integrable (A.column 1 : LoopPlane → EuclideanSpace ℝ (Fin m)) mu :=
    (Lp.memLp (A.column 1)).integrable (by norm_num)
  have hc : Continuous (fun p : LoopPlane => a + b * p 1) := by fun_prop
  have hf : Integrable f mu := (hu.smul b).add (m64Annulus_continuous_smul_integrable hv hc)
  have hfi := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hf
  apply ae_eq_of_integral_contDiff_smul_eq hfi.integral_prod_left.locallyIntegrable
    ((h1.smul (a + b)).sub (h0.smul a)).locallyIntegrable
  intro theta htheta _
  let phi := fun p : LoopPlane => theta (p 0) * (a + b * p 1)
  have htheta1 : ContDiff ℝ 1 theta := htheta.of_le (by simp)
  have hphi : ContDiff ℝ 1 phi :=
    (htheta1.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
      (contDiff_const.add (contDiff_const.mul
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff))
  have hd (p : LoopPlane) :
      fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) = theta (p 0) * b := by
    have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
    have hcomp := (hphi.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (p 1)
      (m64AnnulusPoint_vertical_hasDerivAt (p 0) (p 1))
    rw [hpoint] at hcomp
    have hcalc := (((hasDerivAt_id (p 1)).const_mul b).const_add a).const_mul (theta (p 0))
    exact hcomp.unique (by simpa [phi, Function.comp_def, annulusPoint] using hcalc)
  have hgreen := A.boundary phi hphi
  simp only [hd] at hgreen
  change (∫ x in Icc (0 : ℝ) curvePeriod,
    theta x • ∫ s in Icc (0 : ℝ) 1, f (annulusPoint x s)) =
      ∫ x in Icc (0 : ℝ) curvePeriod, theta x • ((a + b) • e (c1 x) - a • e (c0 x))
  rw [m64Annulus_vertical_average_pairing hf htheta.continuous]
  have hthetaC : Continuous (fun p : LoopPlane => theta (p 0) * b) := by fun_prop
  have hleft := m64Annulus_continuous_smul_integrable hv hphi.continuous
  have hright := m64Annulus_continuous_smul_integrable hu hthetaC
  calc
    _ = (∫ p in S, phi p • A.column 1 p) +
        ∫ p in S, (theta (p 0) * b) • e (A.map p) := by
      rw [← integral_add hleft hright]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by simp only [f, phi, smul_add, mul_smul]; abel
    _ = _ := by
      rw [hgreen]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp [phi, annulusPoint, smul_sub, mul_smul]




theorem M64ObservedWeakAnnulus.radial_trace_averages
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (h0 : Integrable (e ∘ c0) nu) (h1 : Integrable (e ∘ c1) nu) :
    ∀ᵐ x ∂nu,
      (∫ s in Icc (0 : ℝ) 1, e (A.map (annulusPoint x s)) +
        (s - 1) • A.column 1 (annulusPoint x s)) = e (c0 x) ∧
      (∫ s in Icc (0 : ℝ) 1, e (A.map (annulusPoint x s)) +
        s • A.column 1 (annulusPoint x s)) = e (c1 x) := by
  filter_upwards [A.radial_green_average h0 h1 (-1) 1,
    A.radial_green_average h0 h1 0 1] with x hlow hupp
  constructor
  · simpa only [one_smul, one_mul, neg_add_cancel, zero_smul, neg_smul,
      sub_neg_eq_add, zero_add, show ∀ s : ℝ, -1 + s = s - 1 from fun s => by ring,
      sub_self] using hlow
  · simpa only [one_smul, one_mul, zero_add, zero_smul, sub_zero] using hupp





theorem M64ObservedWeakAnnulus.angular_column_integral_eq_zero
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∀ᵐ s ∂sigma, (∫ x in Icc (0 : ℝ) curvePeriod, A.column 0 (annulusPoint x s)) = 0 := by
  have hv : Integrable (A.column 0 : LoopPlane → EuclideanSpace ℝ (Fin m)) mu :=
    (Lp.memLp (A.column 0)).integrable (by norm_num)
  have hi := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hv
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.integral_prod_right.locallyIntegrable
  intro eta heta _
  let Y := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  let phi := eta ∘ Y
  have heta1 : ContDiff ℝ 1 eta := heta.of_le (by simp)
  have hphi : ContDiff ℝ 1 phi := heta1.comp Y.contDiff
  have hd (p : LoopPlane) :
      fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) = 0 := by
    rw [fderiv_comp p (heta1.differentiable (by simp) _) Y.differentiableAt, Y.fderiv]
    simp [Y, ContinuousLinearMap.comp_apply]
  have hseam := A.seam phi hphi (fun _ _ => rfl)
  simp only [hd, zero_smul, integral_zero, add_zero] at hseam
  rw [← hseam, m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _
    (m64Annulus_continuous_smul_integrable hv hphi.continuous)]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => (integral_smul (eta s) _).symm

end PoincareConjecture
