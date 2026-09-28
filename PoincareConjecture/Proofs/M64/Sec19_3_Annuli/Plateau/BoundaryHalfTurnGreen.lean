import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnGreenTests
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "a" => curvePeriod / 2
local notation "v" => annulusPoint (curvePeriod / 2) 0
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)

theorem m64HalfTurnTest_fderiv {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (p : LoopPlane) (i : Fin 2) (w : LoopPlane) :
    fderiv ℝ (fun q => phi (q + w)) p (ei i) = fderiv ℝ phi (p + w) (ei i) := by
  have h := (hp.differentiable (by simp) _).hasFDerivAt.comp p
    ((hasFDerivAt_id p).add_const w)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
    congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (ei i)) h.fderiv

theorem m64HalfTurnTest_piece (phi : LoopPlane → ℝ) (p : LoopPlane) :
    m64HalfTurnPiece (fun q => phi (q + v)) (fun q => phi (q + -v)) p =
      phi (m64AnnulusHalfTurn p) := by
  simp only [m64HalfTurnPiece, m64AnnulusHalfTurn, sub_eq_add_neg]
  split_ifs <;> rfl

theorem m64HalfTurn_vertical_green
    {u V : LoopPlane → E} (hu : Integrable u mu) (hV : Integrable V mu)
    {c0 c1 : ℝ → E} (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p (ei 1) • u p) =
        ∫ x in I, phi (annulusPoint x 1) • c1 x - phi (annulusPoint x 0) • c0 x)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • V (m64AnnulusHalfTurn p)) +
      (∫ p in S, fderiv ℝ phi p (ei 1) • u (m64AnnulusHalfTurn p)) =
      ∫ x in I, phi (annulusPoint x 1) • c1 (m64BoundaryHalfTurn x) -
        phi (annulusPoint x 0) • c0 (m64BoundaryHalfTurn x) := by
  let f := fun p : LoopPlane => phi (p + v)
  let g := fun p : LoopPlane => phi (p + -v)
  have hf : ContDiff ℝ 1 f := hp.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ 1 g := hp.comp (contDiff_id.add contDiff_const)
  have h := m64HalfTurnPiece_vertical_green hu hV
    (hc0.integrableOn_Icc) (hc1.integrableOn_Icc) hgreen hf hg
  have hder (p : LoopPlane) : m64HalfTurnPiece
      (fun q => fderiv ℝ f q (ei 1)) (fun q => fderiv ℝ g q (ei 1)) p =
        fderiv ℝ phi (m64AnnulusHalfTurn p) (ei 1) := by
    simp_rw [f, g, m64HalfTurnTest_fderiv hp]
    exact m64HalfTurnTest_piece (fun q => fderiv ℝ phi q (ei 1)) p
  simp_rw [hder, show ∀ p, m64HalfTurnPiece f g p = phi (m64AnnulusHalfTurn p)
    from m64HalfTurnTest_piece phi] at h
  rw [m64AnnulusHalfTurn_integral_pair hp.continuous.aestronglyMeasurable
    hV.aestronglyMeasurable,
    m64AnnulusHalfTurn_integral_pair
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
      hu.aestronglyMeasurable, h]
  have hint (c : ℝ → E) (hc : Continuous c) (s : ℝ) :
      IntegrableOn (fun x => phi (annulusPoint x s) • c (m64BoundaryHalfTurn x)) I volume := by
    have hci : Integrable c (volume.restrict I) := hc.integrableOn_Icc
    have hcm := m64BoundaryHalfTurn_measurePreserving.integrable_comp_of_integrable hci
    have hpC := hp.continuous.comp (m64Source_annulusPoint_contDiff s).continuous
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact I).exists_bound_of_continuousOn hpC.continuousOn
    exact hcm.bdd_smul C hpC.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hC x hx)
  have hint' (c : ℝ → E) (hc : Continuous c) (s : ℝ) :
      IntegrableOn (fun x => phi (annulusPoint (m64BoundaryHalfTurn x) s) • c x) I volume := by
    have hpC := hp.continuous.comp (m64Source_annulusPoint_contDiff s).continuous
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact I).exists_bound_of_continuousOn hpC.continuousOn
    apply hc.integrableOn_Icc.bdd_smul C
      (hpC.aestronglyMeasurable.comp_quasiMeasurePreserving
        m64BoundaryHalfTurn_measurePreserving.quasiMeasurePreserving)
    filter_upwards [m64BoundaryHalfTurn_measurePreserving.quasiMeasurePreserving.ae
      (ae_restrict_mem measurableSet_Icc)] with x hx
    exact hC _ hx
  simp_rw [m64AnnulusHalfTurn_boundary_point]
  rw [integral_sub (hint' c1 hc1 1) (hint' c0 hc0 0),
    integral_sub (hint c1 hc1 1) (hint c0 hc0 0)]
  congr 1 <;> symm
  · exact m64BoundaryHalfTurn_integral_pair
      (hp.continuous.comp (m64Source_annulusPoint_contDiff 1).continuous).aestronglyMeasurable
      (hc1.integrableOn_Icc : IntegrableOn c1 I volume).aestronglyMeasurable
  · exact m64BoundaryHalfTurn_integral_pair
      (hp.continuous.comp (m64Source_annulusPoint_contDiff 0).continuous).aestronglyMeasurable
      (hc0.integrableOn_Icc : IntegrableOn c0 I volume).aestronglyMeasurable

theorem m64HalfTurn_seam_green
    {u V : LoopPlane → E} (hu : Integrable u mu) (hV : Integrable V mu)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p • V p) + (∫ p in S, fderiv ℝ phi p (ei 0) • u p) = 0)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    (∫ p in S, phi p • V (m64AnnulusHalfTurn p)) +
      (∫ p in S, fderiv ℝ phi p (ei 0) • u (m64AnnulusHalfTurn p)) = 0 := by
  have hadd (s : ℝ) : annulusPoint a s + v = annulusPoint curvePeriod s := by
    ext i; fin_cases i <;> simp [annulusPoint]
  have hsub (s : ℝ) : annulusPoint a s + -v = annulusPoint 0 s := by
    ext i; fin_cases i <;> simp [annulusPoint]
  have hend (s : ℝ) : annulusPoint curvePeriod s + -v = annulusPoint 0 s + v := by
    ext i
    fin_cases i
    · simp [annulusPoint]
      ring
    · simp [annulusPoint]
  have h := m64HalfTurnPiece_seam_green hu hV (0 : E)
    (fun psi hpsi hseam => by simpa only [smul_zero] using hgreen psi hpsi hseam)
    (f := fun q => phi (q + v)) (g := fun q => phi (q + -v))
    (hp.comp (contDiff_id.add contDiff_const)) (hp.comp (contDiff_id.add contDiff_const))
    (fun s hs => by rw [hadd, hsub]; exact hperiod s hs)
    (fun s _ => congrArg phi (hend s))
  simp_rw [m64HalfTurnTest_fderiv hp, m64HalfTurnTest_piece (fun q => fderiv ℝ phi q (ei 0)),
    m64HalfTurnTest_piece phi, smul_zero] at h
  rw [m64AnnulusHalfTurn_integral_pair hp.continuous.aestronglyMeasurable
    hV.aestronglyMeasurable,
    m64AnnulusHalfTurn_integral_pair
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
      hu.aestronglyMeasurable]
  exact h

end PoincareConjecture
