import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteRicciTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem m64Annulus_modulusRicci_neg_integral_le
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusDomain)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {R : ℝ} (hRic : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      -D.ricci q v v ≤ R * g.inner q v v) :
    -(∫ p in m64AnnulusDomain,
      r * D.ricci (A.map p)
        (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      r⁻¹ * D.ricci (A.map p)
        (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1))) ≤
      2 * R * A.area := by
  let E := m64ModulusEnergyDensity g r A.map
  let T := fun p =>
    r * D.ricci (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
    r⁻¹ * D.ricci (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  have hEI : IntegrableOn E m64AnnulusDomain volume :=
    m64_weightedGram_integrable_of_ae_modulus_conformal A hr hconformal
  have hTI : IntegrableOn T m64AnnulusDomain volume :=
    m64Annulus_modulusRicci_integrable D r hA
  have hpoint (p : LoopPlane) : -T p ≤ 2 * R * E p := by
    have h0 := mul_le_mul_of_nonneg_left
      (hRic (A.map p) (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 0)))
      hr.le
    have h1 := mul_le_mul_of_nonneg_left
      (hRic (A.map p) (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
      (inv_nonneg.mpr hr.le)
    dsimp only [T, E, m64ModulusEnergyDensity, m60AreaGram]
    nlinarith only [h0, h1]
  have hbound := integral_mono hTI.neg (hEI.const_mul (2 * R)) hpoint
  change (∫ p in m64AnnulusDomain, -T p) ≤
    ∫ p in m64AnnulusDomain, 2 * R * E p at hbound
  have harea : (∫ p in m64AnnulusDomain, E p) = A.area :=
    m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  rw [integral_neg, integral_const_mul, harea] at hbound
  exact hbound

end PoincareConjecture
