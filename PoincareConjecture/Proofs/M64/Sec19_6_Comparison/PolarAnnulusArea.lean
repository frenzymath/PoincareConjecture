import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarAnnulusDensity
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarAnnulusRegularity
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarForwardGeometry
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarForwardJacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

theorem m64Annulus_polar_area_le
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) :
    (∫ z in (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet,
      m60AreaDensity g (m64PolarAnnulusMap A.map) z) ≤ A.area := by
  let F := m64PolarAnnulusMap A.map
  have hderiv : ∀ p ∈ m64PolarSource,
      HasFDerivWithinAt m64PolarForwardMap (fderiv ℝ m64PolarForwardMap p)
        m64PolarSource p := by
    intro p _
    exact (m64PolarForwardMap_hasFDerivAt p).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hFint : IntegrableOn (m60AreaDensity g F)
      (m64PolarForwardMap '' m64PolarSource) volume :=
    (m64Annulus_polar_area_integrable A).mono_set m64PolarForwardMap_image_subset
  have htrans := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    m64PolarSource_open.measurableSet hderiv m64PolarForwardMap_injOn
      (m60AreaDensity g F)).mp hFint
  simp only [smul_eq_mul] at htrans
  have hpoint (p : LoopPlane) (hp : p ∈ m64PolarSource) :
      |(fderiv ℝ m64PolarForwardMap p).det| *
        m60AreaDensity g F (m64PolarForwardMap p) ≤ m60AreaDensity g A.map p := by
    have hp1 : -1 < p 1 := by linarith [hp.2.2.1]
    let r : ℝ := (1 / 2 : ℝ) * (p 1 + 1)
    have hr : 0 < r := by dsimp only [r]; linarith
    have hrect : annulusPoint (p 0) (2 * r - 1) = p := by
      ext i
      fin_cases i
      · rfl
      · change 2 * ((1 / 2 : ℝ) * (p 1 + 1)) - 1 = p 1
        ring
    have h := m64PolarAnnulusMap_density_le g A.periodic hr (p 0)
    rw [hrect] at h
    change r * m60AreaDensity g F (m64PolarForwardMap p) ≤
      2 * m60AreaDensity g A.map p at h
    rw [m64PolarForwardMap_abs_det hp1]
    dsimp only [r] at h
    nlinarith only [h]
  have hbound : ∀ᵐ p ∂volume.restrict m64PolarSource,
      |(fderiv ℝ m64PolarForwardMap p).det| *
        m60AreaDensity g F (m64PolarForwardMap p) ≤ m60AreaDensity g A.map p := by
    filter_upwards [ae_restrict_mem m64PolarSource_open.measurableSet] with p hp
    exact hpoint p hp
  calc
    _ = ∫ z in m64PolarForwardMap '' m64PolarSource, m60AreaDensity g F z :=
      setIntegral_congr_set m64PolarForwardMap_image_ae_eq.symm
    _ = ∫ p in m64PolarSource, |(fderiv ℝ m64PolarForwardMap p).det| *
        m60AreaDensity g F (m64PolarForwardMap p) := by
      simpa only [smul_eq_mul] using
        integral_image_eq_integral_abs_det_fderiv_smul volume
          m64PolarSource_open.measurableSet hderiv m64PolarForwardMap_injOn
          (m60AreaDensity g F)
    _ ≤ ∫ p in m64PolarSource, m60AreaDensity g A.map p :=
      integral_mono_ae htrans (A.area_integrable.mono_set m64PolarSource_subset) hbound
    _ = A.area := setIntegral_congr_set m64PolarSource_ae_eq_domain

end PoincareConjecture
