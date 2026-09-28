import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open Proofs.M58

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (-(1 / 2 : ℝ)) (1 / 2))
local notation "PolarBand" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (-Real.pi) Real.pi)

private def angleScale : Cover →L[ℝ] Cover :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 0; 0, 2 * Real.pi]).toContinuousLinearMap

private theorem angleScale_apply (z : Cover) :
    angleScale z = (z.1, 2 * Real.pi * z.2) := by
  simp [angleScale, Matrix.toLin_finTwoProd_toContinuousLinearMap]

private theorem angleScale_det : angleScale.det = 2 * Real.pi := by
  simp [angleScale, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]

private theorem angleScale_injective : Function.Injective angleScale := by
  intro x y h
  simp only [angleScale_apply, Prod.mk.injEq] at h
  exact Prod.ext h.1 (mul_left_cancel₀
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) h.2)

private theorem angleScale_image : angleScale '' Band = PolarBand := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  ext z
  constructor
  · rintro ⟨p, hpband, rfl⟩
    rw [angleScale_apply]
    refine ⟨hpband.1, ?_, ?_⟩
    · have h := mul_lt_mul_of_pos_left hpband.2.1 hp
      nlinarith
    · have h := mul_lt_mul_of_pos_left hpband.2.2 hp
      nlinarith
  · intro hz
    refine ⟨(z.1, z.2 / (2 * Real.pi)), ⟨hz.1, ?_, ?_⟩, ?_⟩
    · apply (lt_div_iff₀ hp).mpr
      nlinarith [hz.2.1]
    · apply (div_lt_iff₀ hp).mpr
      nlinarith [hz.2.2]
    · rw [angleScale_apply]
      simp only [mul_div_cancel₀ _ hp.ne']

theorem scalarCoverMap_eq_polar (z : Cover) :
    scalarCoverMap z = z.1 • angularPoint (2 * Real.pi * z.2) := by
  have h := scalarCoverMap_polar_relation z.1 (2 * Real.pi * z.2)
  have ht : 2 * Real.pi * z.2 / (2 * Real.pi) = z.2 := by field_simp
  simpa only [ht, Prod.mk.eta] using h

theorem scalarAnnulus_integral_cover (F : Plane → ℝ) :
    (∫ x in scalarAnnulus, F x) =
      ∫ z in Band, (2 * Real.pi * z.1) * F (scalarCoverMap z) := by
  rw [scalarAnnulus_integral_polar]
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume (s := Band)
    (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun z _ => (angleScale.hasFDerivAt (x := z)).hasFDerivWithinAt)
    angleScale_injective.injOn
    (fun p : Cover => p.1 * F (p.1 • angularPoint p.2))
  erw [angleScale_image] at h
  calc
    _ = ∫ z in Band, |angleScale.det| •
        ((angleScale z).1 * F ((angleScale z).1 • angularPoint (angleScale z).2)) := h
    _ = _ := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro z _
      dsimp only
      rw [angleScale_det, abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
        angleScale_apply, scalarCoverMap_eq_polar]
      simp only [smul_eq_mul]
      ring

theorem scalarAnnulus_integrable_cover {F : Plane → ℝ}
    (hF : IntegrableOn F scalarAnnulus) :
    IntegrableOn (fun z : Cover => (2 * Real.pi * z.1) * F (scalarCoverMap z)) Band := by
  have hp := scalarAnnulus_integrable_polar hF
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (s := Band)
    (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun z _ => (angleScale.hasFDerivAt (x := z)).hasFDerivWithinAt)
    angleScale_injective.injOn
    (fun p : Cover => p.1 * F (p.1 • angularPoint p.2))).mp (by
      erw [angleScale_image]
      exact hp)
  apply h.congr_fun ?_ (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z _
  dsimp only
  rw [angleScale_det, abs_of_pos (mul_pos (by norm_num) Real.pi_pos),
    angleScale_apply, scalarCoverMap_eq_polar]
  simp only [smul_eq_mul]
  ring

end PoincareConjecture.M64Uniformization
