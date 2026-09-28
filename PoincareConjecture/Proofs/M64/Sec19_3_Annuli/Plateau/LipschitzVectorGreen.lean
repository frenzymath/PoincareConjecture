import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzRectangleGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzObservedColumns











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace PoincareConjecture

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64_lipschitz_vector_green_integrable {f : LoopPlane → E} {phi : LoopPlane → ℝ}
    {K : ℝ≥0} (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    IntegrableOn (fun p => phi p • fderiv ℝ f p (EuclideanSpace.single i 1)) S volume ∧
      IntegrableOn (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1) • f p) S volume := by
  constructor
  · apply Integrable.of_eval_piLp
    intro b
    have hh := (m64_lipschitz_green_integrable (m64_lipschitz_coordinate hf b) hphi i).1
    apply hh.congr
    filter_upwards [m64_vector_partial_coordinate_ae hdiff i b] with p hp
    simpa only [PiLp.smul_apply, smul_eq_mul] using congrArg (fun t : ℝ => phi p * t) hp
  · apply Integrable.of_eval_piLp
    intro b
    simpa only [IntegrableOn, PiLp.smul_apply, smul_eq_mul] using
      (m64_lipschitz_green_integrable (m64_lipschitz_coordinate hf b) hphi i).2



theorem m64Annulus_vertical_green_lipschitzOn_vector
    {f : LoopPlane → E} {phi : LoopPlane → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • f p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • f (annulusPoint x 1) -
          phi (annulusPoint x 0) • f (annulusPoint x 0) := by
  obtain ⟨hleft, hright⟩ := m64_lipschitz_vector_green_integrable hf hdiff hphi 1
  have htrace (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContinuousOn (fun x => f (annulusPoint x s)) (Icc (0 : ℝ) curvePeriod) :=
    hf.continuousOn.comp (m64AnnulusPoint_horizontal_lipschitz s).continuous.continuousOn
      (fun x hx => ⟨hx.1, hx.2, hs.1, hs.2⟩)
  have hp (s : ℝ) : Continuous (fun x => phi (annulusPoint x s)) :=
    hphi.continuous.comp (m64AnnulusPoint_horizontal_lipschitz s).continuous
  have hb : IntegrableOn (fun x => phi (annulusPoint x 1) • f (annulusPoint x 1) -
      phi (annulusPoint x 0) • f (annulusPoint x 0)) (Icc (0 : ℝ) curvePeriod) volume :=
    (((hp 1).continuousOn.smul (htrace 1 (by norm_num))).sub
      ((hp 0).continuousOn.smul (htrace 0 (by norm_num)))).integrableOn_compact isCompact_Icc
  apply PiLp.ext
  intro b
  rw [PiLp.add_apply, eval_integral_piLp hleft.eval_piLp b,
    eval_integral_piLp hright.eval_piLp b, eval_integral_piLp hb.eval_piLp b]
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have hc : (∫ p in S, phi p *
      fderiv ℝ (fun q => f q b) p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ p in S, phi p * (fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) b :=
    integral_congr_ae ((m64_vector_partial_coordinate_ae hdiff 1 b).mono
      fun p hp => congrArg (fun t : ℝ => phi p * t) hp)
  rw [← hc]
  exact m64Annulus_vertical_green_lipschitzOn (m64_lipschitz_coordinate hf b) hphi



theorem m64Annulus_horizontal_green_lipschitzOn_vector
    {f : LoopPlane → E} {phi : LoopPlane → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p • fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • f p) =
      ∫ s in Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) • f (annulusPoint curvePeriod s) -
          phi (annulusPoint 0 s) • f (annulusPoint 0 s) := by
  obtain ⟨hleft, hright⟩ := m64_lipschitz_vector_green_integrable hf hdiff hphi 0
  have htrace (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      ContinuousOn (fun s => f (annulusPoint x s)) (Icc (0 : ℝ) 1) :=
    hf.continuousOn.comp (m64AnnulusPoint_vertical_lipschitz x).continuous.continuousOn
      (fun s hs => ⟨hx.1, hx.2, hs.1, hs.2⟩)
  have hp (x : ℝ) : Continuous (fun s => phi (annulusPoint x s)) :=
    hphi.continuous.comp (m64AnnulusPoint_vertical_lipschitz x).continuous
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hb : IntegrableOn (fun s => phi (annulusPoint curvePeriod s) •
      f (annulusPoint curvePeriod s) - phi (annulusPoint 0 s) • f (annulusPoint 0 s))
      (Icc (0 : ℝ) 1) volume :=
    (((hp curvePeriod).continuousOn.smul (htrace curvePeriod ⟨hP, le_rfl⟩)).sub
      ((hp 0).continuousOn.smul (htrace 0 ⟨le_rfl, hP⟩))).integrableOn_compact isCompact_Icc
  apply PiLp.ext
  intro b
  rw [PiLp.add_apply, eval_integral_piLp hleft.eval_piLp b,
    eval_integral_piLp hright.eval_piLp b, eval_integral_piLp hb.eval_piLp b]
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have hc : (∫ p in S, phi p *
      fderiv ℝ (fun q => f q b) p (EuclideanSpace.single (0 : Fin 2) 1)) =
      ∫ p in S, phi p * (fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) b :=
    integral_congr_ae ((m64_vector_partial_coordinate_ae hdiff 0 b).mono
      fun p hp => congrArg (fun t : ℝ => phi p * t) hp)
  rw [← hc]
  exact m64Annulus_horizontal_green_lipschitzOn (m64_lipschitz_coordinate hf b) hphi



theorem m64Annulus_periodic_green_lipschitzOn_vector
    {f : LoopPlane → E} {phi : LoopPlane → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (hphi : ContDiff ℝ 1 phi)
    (hfseam : ∀ s ∈ Icc (0 : ℝ) 1, f (annulusPoint curvePeriod s) = f (annulusPoint 0 s))
    (hpseam : ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    (∫ p in S, phi p • fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • f p) = 0 := by
  rw [m64Annulus_horizontal_green_lipschitzOn_vector hf hdiff hphi]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [hfseam s hs, hpseam s hs, sub_self]
  rfl

end PoincareConjecture
