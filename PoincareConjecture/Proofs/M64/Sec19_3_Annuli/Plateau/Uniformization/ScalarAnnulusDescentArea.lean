import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAnnulusDescent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarStandardCylinder
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarRoughAreaChange
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderAdmission













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)





theorem scalarAnnulusDescent_comp_standardCylinder
    {M : Type*} {f : Plane → M} {F : Plane → M}
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = scalarAnnulusCoverLift f z)
    {p : Plane} (hp : p ∈ Strip) : (F ∘ scalarStandardCylinderMap) p = f p := by
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  rw [Function.comp_apply, scalarStandardCylinderMap, hdesc _ (by
    change 0 < p 1 + 1
    linarith [hp.1])]
  unfold scalarAnnulusCoverLift scalarAnnulusClamp
  simp only [scalarCylinderCoordinate_apply, Prod.fst_add, Prod.snd_add, add_zero,
    add_sub_cancel_right, ← mul_assoc, mul_inv_cancel₀ hP, one_mul,
    projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1)
      (show p 1 ∈ Icc (0 : ℝ) 1 from ⟨hp.1.le, hp.2.le⟩)]
  congr 1
  ext i
  fin_cases i <;> rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem scalarAnnulusDescent_density
    (g : RiemannianMetric n M) {f : Plane → M} {F : Plane → M}
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = scalarAnnulusCoverLift f z)
    {p : Plane} (hp : p ∈ Strip) :
    |(fderiv ℝ scalarStandardCylinderMap p).det| *
      m60AreaDensity g F (scalarStandardCylinderMap p) = m60AreaDensity g f p := by
  rw [← scalarAreaDensity_comp_localDiffeomorph g F
    (scalarStandardCylinderMap_smooth.contDiffAt.of_le (by simp))
    (scalarStandardCylinderMap_invertible hp)]
  apply m60AreaDensity_congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous).mem_nhds hp]
    with q hq
  exact scalarAnnulusDescent_comp_standardCylinder hdesc hq





theorem scalarAnnulusDescent_area
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    {F : Plane → M}
    (hdesc : ∀ z : Cover, 0 < z.1 → F (scalarCoverMap z) = scalarAnnulusCoverLift A.map z) :
    IntegrableOn (m60AreaDensity g F) scalarAnnulus ∧
      (∫ p in scalarAnnulus, m60AreaDensity g F p) = A.area := by
  have hD (p : Plane) : HasFDerivAt scalarStandardCylinderMap
      (fderiv ℝ scalarStandardCylinderMap p) p :=
    (scalarStandardCylinderMap_smooth.differentiable (by simp) p).hasFDerivAt
  have hchange := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable (fun p _ => (hD p).hasFDerivWithinAt)
    scalarStandardCylinderMap_injOn (m60AreaDensity g F)
  rw [scalarStandardCylinderMap_image] at hchange
  have hAI : IntegrableOn (m60AreaDensity g A.map) scalarCylinderFundamental :=
    (integrableOn_congr_set_ae scalarCylinderFundamental_ae_eq_domain).mpr A.area_integrable
  have hFI : IntegrableOn (m60AreaDensity g F) scalarAnnulus := by
    apply hchange.mpr
    apply hAI.congr_fun _ scalarCylinderFundamental_measurable
    intro p hp
    simpa only [smul_eq_mul] using (scalarAnnulusDescent_density g hdesc hp.1).symm
  refine ⟨hFI, ?_⟩
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable (fun p _ => (hD p).hasFDerivWithinAt)
    scalarStandardCylinderMap_injOn (m60AreaDensity g F)
  rw [scalarStandardCylinderMap_image] at hi
  calc
    (∫ p in scalarAnnulus, m60AreaDensity g F p) =
        ∫ p in scalarCylinderFundamental,
          |(fderiv ℝ scalarStandardCylinderMap p).det| *
            m60AreaDensity g F (scalarStandardCylinderMap p) := by
      simpa only [smul_eq_mul] using hi
    _ = ∫ p in scalarCylinderFundamental, m60AreaDensity g A.map p :=
      setIntegral_congr_fun scalarCylinderFundamental_measurable
        (fun _ hp => scalarAnnulusDescent_density g hdesc hp.1)
    _ = A.area := setIntegral_congr_set scalarCylinderFundamental_ae_eq_domain

end PoincareConjecture.M64Uniformization
