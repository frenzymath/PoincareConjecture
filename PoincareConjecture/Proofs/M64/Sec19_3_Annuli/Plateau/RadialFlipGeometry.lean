import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PlaneReflection

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

def m64AnnulusRadialFlip : LoopPlane ≃ₜ LoopPlane :=
  m60PlaneReflection.toHomeomorph.trans (Homeomorph.addLeft (annulusPoint 0 1))

theorem m64AnnulusRadialFlip_apply (p : LoopPlane) :
    m64AnnulusRadialFlip p = annulusPoint 0 1 + m60PlaneReflection p := rfl

theorem m64AnnulusRadialFlip_point (x s : ℝ) :
    m64AnnulusRadialFlip (annulusPoint x s) = annulusPoint x (1 - s) := by
  ext i
  fin_cases i <;> simp [m64AnnulusRadialFlip_apply, m60PlaneReflection_apply, annulusPoint,
    sub_eq_add_neg]

theorem m64AnnulusRadialFlip_involutive : Function.Involutive m64AnnulusRadialFlip := by
  intro p
  ext i
  fin_cases i <;> simp [m64AnnulusRadialFlip_apply, m60PlaneReflection_apply, annulusPoint]

theorem m64AnnulusRadialFlip_contDiff : ContDiff ℝ ∞ m64AnnulusRadialFlip :=
  contDiff_const.add m60PlaneReflection.toContinuousLinearEquiv.contDiff

theorem m64AnnulusRadialFlip_preimage_interior :
    m64AnnulusRadialFlip ⁻¹' interior m64AnnulusDomain = interior m64AnnulusDomain := by
  ext p
  simp only [mem_preimage, m64AnnulusInterior_coordinates, m64AnnulusRadialFlip_apply,
    PiLp.add_apply, m60PlaneReflection_apply, annulusPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, ite_true, zero_add,
    show (1 : Fin 2) ≠ 0 from by decide, ite_false]
  constructor <;> rintro ⟨h0, hP, h1, h2⟩ <;> exact ⟨h0, hP, by linarith, by linarith⟩

theorem m64AnnulusRadialFlip_measurePreserving :
    MeasurePreserving m64AnnulusRadialFlip volume volume :=
  (measurePreserving_add_left (volume : Measure LoopPlane) (annulusPoint 0 1)).comp
    m60PlaneReflection.measurePreserving

theorem m64AnnulusRadialFlip_restrict_measurePreserving :
    MeasurePreserving m64AnnulusRadialFlip
      (volume.restrict (interior m64AnnulusDomain))
      (volume.restrict (interior m64AnnulusDomain)) := by
  have h := m64AnnulusRadialFlip_measurePreserving.restrict_preimage_emb
    m64AnnulusRadialFlip.measurableEmbedding (interior m64AnnulusDomain)
  rwa [m64AnnulusRadialFlip_preimage_interior] at h

theorem m64AnnulusRadialFlip_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : LoopPlane → E) :
    (∫ p in interior m64AnnulusDomain, f (m64AnnulusRadialFlip p)) =
      ∫ p in interior m64AnnulusDomain, f p :=
  m64AnnulusRadialFlip_restrict_measurePreserving.integral_comp
    m64AnnulusRadialFlip.measurableEmbedding f

theorem m64AnnulusRadialFlip_fderiv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : LoopPlane → E} (hf : Differentiable ℝ f) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (f ∘ m64AnnulusRadialFlip) p (EuclideanSpace.single i 1) =
      (if i = 0 then (1 : ℝ) else -1) •
        fderiv ℝ f (m64AnnulusRadialFlip p) (EuclideanSpace.single i 1) := by
  have hflip : HasFDerivAt m64AnnulusRadialFlip
      m60PlaneReflection.toContinuousLinearEquiv.toContinuousLinearMap p :=
    m60PlaneReflection.toContinuousLinearEquiv.hasFDerivAt.const_add (annulusPoint 0 1)
  rw [fderiv_comp p (hf _) hflip.differentiableAt, ContinuousLinearMap.comp_apply, hflip.fderiv]
  have hb : m60PlaneReflection (EuclideanSpace.single i 1) =
      (if i = 0 then (1 : ℝ) else -1) • EuclideanSpace.single i 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [m60PlaneReflection_apply]
  change fderiv ℝ f (m64AnnulusRadialFlip p) (m60PlaneReflection (EuclideanSpace.single i 1)) = _
  rw [hb, map_smul]

theorem m64AnnulusRadialFlip_green
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u V : LoopPlane → E) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in interior m64AnnulusDomain, phi p •
      ((if i = 0 then (1 : ℝ) else -1) • V (m64AnnulusRadialFlip p))) +
      (∫ p in interior m64AnnulusDomain,
        fderiv ℝ phi p (EuclideanSpace.single i 1) • u (m64AnnulusRadialFlip p)) =
      (if i = 0 then (1 : ℝ) else -1) •
        ((∫ p in interior m64AnnulusDomain, (phi ∘ m64AnnulusRadialFlip) p • V p) +
          ∫ p in interior m64AnnulusDomain,
            fderiv ℝ (phi ∘ m64AnnulusRadialFlip) p (EuclideanSpace.single i 1) • u p) := by
  rw [smul_add]
  congr 1
  · calc
      _ = ∫ p in interior m64AnnulusDomain, (if i = 0 then (1 : ℝ) else -1) •
          ((phi ∘ m64AnnulusRadialFlip) (m64AnnulusRadialFlip p) •
            V (m64AnnulusRadialFlip p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        simp only [Function.comp_apply]
        rw [m64AnnulusRadialFlip_involutive p]
        exact smul_comm (phi p) (if i = 0 then (1 : ℝ) else -1) (V (m64AnnulusRadialFlip p))
      _ = ∫ p in interior m64AnnulusDomain, (if i = 0 then (1 : ℝ) else -1) •
          ((phi ∘ m64AnnulusRadialFlip) p • V p) :=
        m64AnnulusRadialFlip_integral (fun p =>
          (if i = 0 then (1 : ℝ) else -1) • ((phi ∘ m64AnnulusRadialFlip) p • V p))
      _ = _ := integral_smul _ _
  · calc
      _ = ∫ p in interior m64AnnulusDomain, (if i = 0 then (1 : ℝ) else -1) •
          (fderiv ℝ (phi ∘ m64AnnulusRadialFlip) (m64AnnulusRadialFlip p)
            (EuclideanSpace.single i 1) • u (m64AnnulusRadialFlip p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [m64AnnulusRadialFlip_fderiv_comp (hp.differentiable (by simp)),
          m64AnnulusRadialFlip_involutive]
        split_ifs <;> simp
      _ = ∫ p in interior m64AnnulusDomain, (if i = 0 then (1 : ℝ) else -1) •
          (fderiv ℝ (phi ∘ m64AnnulusRadialFlip) p (EuclideanSpace.single i 1) • u p) :=
        m64AnnulusRadialFlip_integral (fun p => (if i = 0 then (1 : ℝ) else -1) •
          (fderiv ℝ (phi ∘ m64AnnulusRadialFlip) p (EuclideanSpace.single i 1) • u p))
      _ = _ := integral_smul _ _

end PoincareConjecture
