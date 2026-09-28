import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ConformalMinimumStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyInterface
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ClosedRectangleEnergyVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimumStationarity
import Mathlib.Analysis.Calculus.LocalExtr.Basic













set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

private theorem hasDerivAt_zero_of_area_energy_squeeze
    {f F : ℝ → ℝ} {x : ℝ} (hF : HasDerivAt F 0 x)
    (hcenter : f x = F x)
    (hlower : ∀ᶠ y in 𝓝 x, f x ≤ f y)
    (hupper : ∀ᶠ y in 𝓝 x, f y ≤ F y) : HasDerivAt f 0 x := by
  have hbound : (fun y => f y - f x) =O[𝓝 x] (fun y => F y - F x) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hlower, hupper] with y hlo hhi
    have hFnonneg : 0 ≤ F y - F x := by
      rw [← hcenter]
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg hFnonneg]
    rw [← hcenter]
    linarith
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using hbound.trans_isLittleO
    (show (fun y => F y - F x) =o[𝓝 x] (fun y => y - x) from by
      simpa only [smul_zero, sub_zero] using hF.isLittleO)






theorem m64Annulus_area_hasDerivAt_zero_of_conformal_minimum
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v)
    (hadmissible : ∀ s ∈ Ioo (-epsilon) epsilon,
      ∃ B : M64Annulus g c0 c1, B.map = fun p => v (s, p))
    (hcenter : ∀ p, v (0, p) = A.map p) :
    HasDerivAt (fun s => m64AnnulusArea g (fun p => v (s, p))) 0 0 := by
  let E := fun s => ∫ p in m64AnnulusDomain,
    m60EnergyDensity g (fun z => v (s, z)) p
  let a := fun s => m64AnnulusArea g (fun z => v (s, z))
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hmapzero : (fun z => v (0, z)) = A.map := funext hcenter
  have harea0 : a 0 = A.area := by
    simp only [a, hmapzero, M64Annulus.area]
  have henergy0 : E 0 = A.area := by
    simp only [E, hmapzero]
    exact m64Annulus_energy_eq_area_of_ae_conformal A hconformal
  have hint (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      IntegrableOn (m60EnergyDensity g (fun z => v (s, z)))
        m64AnnulusDomain volume := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    have hEq : EqOn B.map (fun p => v (s, p)) m64AnnulusDomain := by
      intro p hp
      exact congrFun hB p
    exact B.energy_integrable.congr
      (m64Annulus_energyDensity_ae_eq_of_eqOn g hEq)
  have hcomparison (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      A.area ≤ a s ∧ a s ≤ E s := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    have hEq : EqOn B.map (fun p => v (s, p)) m64AnnulusDomain := by
      intro p hp
      exact congrFun hB p
    have hBarea : B.area = a s :=
      integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g hEq)
    have hBenergy : (∫ p in m64AnnulusDomain,
        m60EnergyDensity g B.map p) = E s :=
      integral_congr_ae (m64Annulus_energyDensity_ae_eq_of_eqOn g hEq)
    constructor
    · rw [hminimum, ← hBarea]
      exact m64LeastAnnulusArea_le_annulus B
    · rw [← hBarea]
      exact (B.area_le_energy m64AnnulusDomain_measurableSet B.energy_integrable).trans_eq
        hBenergy
  have hlocal : IsLocalMin E 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    rw [henergy0]
    exact (hcomparison s hs).1.trans (hcomparison s hs).2
  have hEderiv : HasDerivAt E 0 0 := by
    have hderiv := (m64AnnulusEnergy_hasDerivAt_of_smooth_variation
      g v hv 0).2
    have hdE : DifferentiableAt ℝ E 0 := hderiv.differentiableAt
    simpa only [hlocal.deriv_eq_zero] using hdE.hasDerivAt
  exact hasDerivAt_zero_of_area_energy_squeeze hEderiv
    (harea0.trans henergy0.symm)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      change a 0 ≤ a s
      rw [harea0]
      exact (hcomparison s hs).1)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact (hcomparison s hs).2)






theorem m64AnnulusAreaStationary_of_conformal_minimum
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    M64AnnulusAreaStationary A := by
  intro epsilon hepsilon v hv hadmissible hcenter
  let E := fun s => ∫ p in m64AnnulusDomain,
    m60EnergyDensity g (fun z => v (s, z)) p
  let a := fun s => m64AnnulusArea g (fun z => v (s, z))
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have harea0 : a 0 = A.area :=
    integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g hcenter)
  have henergy0 : E 0 = A.area := by
    calc
      E 0 = ∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p :=
        integral_congr_ae (m64Annulus_energyDensity_ae_eq_of_eqOn g hcenter)
      _ = A.area := m64Annulus_energy_eq_area_of_ae_conformal A hconformal
  have hcomparison (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      A.area ≤ a s ∧ a s ≤ E s := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    have hEq : EqOn B.map (fun p => v (s, p)) m64AnnulusDomain := by
      intro p hp
      exact congrFun hB p
    have hBarea : B.area = a s :=
      integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g hEq)
    have hBenergy : (∫ p in m64AnnulusDomain,
        m60EnergyDensity g B.map p) = E s :=
      integral_congr_ae (m64Annulus_energyDensity_ae_eq_of_eqOn g hEq)
    constructor
    · rw [hminimum, ← hBarea]
      exact m64LeastAnnulusArea_le_annulus B
    · rw [← hBarea]
      exact (B.area_le_energy m64AnnulusDomain_measurableSet B.energy_integrable).trans_eq
        hBenergy
  have hlocal : IsLocalMin E 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    rw [henergy0]
    exact (hcomparison s hs).1.trans (hcomparison s hs).2
  have hEderiv : HasDerivAt E 0 0 := by
    have hv' : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
        (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hv
    have hdE : DifferentiableAt ℝ E 0 :=
      m64AnnulusEnergy_differentiableAt_of_closed_smooth_variation g hepsilon hv'
    simpa only [hlocal.deriv_eq_zero] using hdE.hasDerivAt
  exact hasDerivAt_zero_of_area_energy_squeeze hEderiv
    (harea0.trans henergy0.symm)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      change a 0 ≤ a s
      rw [harea0]
      exact (hcomparison s hs).1)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact (hcomparison s hs).2)






theorem m64AnnulusAreaStationary_of_modulus_conformal_minimum
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    M64AnnulusAreaStationary A := by
  intro epsilon hepsilon v hv hadmissible hcenter
  let E := fun s => ∫ p in m64AnnulusDomain,
    m64ModulusEnergyDensity g r (fun z => v (s, z)) p
  let a := fun s => m64AnnulusArea g (fun z => v (s, z))
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have harea0 : a 0 = A.area :=
    integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g hcenter)
  have henergy0 : E 0 = A.area := by
    calc
      E 0 = m64ClassicalWeightedGramEnergy g A r :=
        integral_congr_ae (m64ModulusEnergyDensity_ae_eq_of_eqOn g r hcenter)
      _ = A.area := m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  have hcomparison (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      A.area ≤ a s ∧ a s ≤ E s := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    have hEq : EqOn B.map (fun p => v (s, p)) m64AnnulusDomain := by
      intro p hp
      exact congrFun hB p
    have hBarea : B.area = a s :=
      integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g hEq)
    have hBenergy : m64ClassicalWeightedGramEnergy g B r = E s :=
      integral_congr_ae (m64ModulusEnergyDensity_ae_eq_of_eqOn g r hEq)
    constructor
    · rw [hminimum, ← hBarea]
      exact m64LeastAnnulusArea_le_annulus B
    · rw [← hBarea]
      exact (B.area_le_weightedGramEnergy hr (B.weightedGramEnergy_integrable r)).trans_eq
        hBenergy
  have hlocal : IsLocalMin E 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    rw [henergy0]
    exact (hcomparison s hs).1.trans (hcomparison s hs).2
  have hEderiv : HasDerivAt E 0 0 := by
    have hv' : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
        (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hv
    have hdE : DifferentiableAt ℝ E 0 := by
      have hgram := m64AnnulusGramEnergy_differentiableAt_of_closed_smooth_variation g
        ![r, r⁻¹] hepsilon hv'
      convert hgram using 1
      funext s
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simp only [m64ModulusEnergyDensity, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        ring
    simpa only [hlocal.deriv_eq_zero] using hdE.hasDerivAt
  exact hasDerivAt_zero_of_area_energy_squeeze hEderiv
    (harea0.trans henergy0.symm)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      change a 0 ≤ a s
      rw [harea0]
      exact (hcomparison s hs).1)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact (hcomparison s hs).2)

end PoincareConjecture
