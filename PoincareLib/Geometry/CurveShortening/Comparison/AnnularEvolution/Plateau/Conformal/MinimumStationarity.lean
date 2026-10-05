import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Supported.AnnulusEnergyVariation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.UniformizationEnergy
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.WeakMinimizer
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.DensityCongruence
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Supported stationarity of an attained conformal annulus

A conformal area minimum is a Dirichlet-energy minimum. The actual supported
energy variation is differentiable, so its derivative vanishes. The area
variation lies between the attained area and the energy variation; this
gives its derivative zero even at rank-zero branch points.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

private theorem hasDerivAt_zero_of_squeezed_minimum
    {f F : ℝ → ℝ} {x : ℝ} (hF : HasDerivAt F 0 x)
    (hcenter : f x = F x)
    (hlower : ∀ᶠ y in 𝓝 x, f x ≤ f y)
    (hupper : ∀ᶠ y in 𝓝 x, f y ≤ F y) : HasDerivAt f 0 x := by
  have hbound : (fun y => f y - f x) =O[𝓝 x] (fun y => F y - F x) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hlower, hupper] with y hlo hhi
    have hFnonneg : 0 ≤ F y - F x := by rw [← hcenter]; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg hFnonneg]
    rw [← hcenter]
    linarith
  apply HasDerivAt.of_isLittleO
  simpa only [smul_zero, sub_zero] using hbound.trans_isLittleO
    (show (fun y => F y - F x) =o[𝓝 x] (fun y => y - x) from by
      simpa only [smul_zero, sub_zero] using hF.isLittleO)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

/-- The ordinary Dirichlet energy equals the actual area for an a.e. conformal annulus,
including its rank-zero locus. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64Annulus_energy_eq_area_of_ae_conformal
    (A : M64Annulus g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    (∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p) = A.area := by
  have h := m64_weightedEnergy_eq_area_of_ae_modulus_conformal A
    (r := 1) zero_lt_one (by simpa only [inv_one, one_mul] using hconformal)
  calc
    _ = m64ClassicalWeightedGramEnergy g A 1 := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [m60EnergyDensity, Matrix.trace_fin_two, inv_one, one_mul]
      ring
    _ = A.area := h

variable [CompactSpace M] [T2Space M]

/-- Every actual two-sided admissible variation supported in an interior compact set is
stationary at an attained conformal area minimum. Both the energy and area derivatives are
proved, with no immersion or branch-rank hypothesis and no assumed first-variation identity.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Annulus_supported_stationarity_of_conformal_minimum_of_eqOn
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {O K : Set LoopPlane} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hKdomain : K ⊆ m64AnnulusDomain)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hadmissible : ∀ s ∈ Ioo (-epsilon) epsilon,
      ∃ B : M64Annulus g c0 c1, EqOn B.map (fun p => v (s, p)) m64AnnulusDomain)
    (hcenter : ∀ p, v (0, p) = A.map p)
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∉ K,
      v (s, z) = v (0, z)) :
    HasDerivAt
      (fun s => ∫ p in m64AnnulusDomain, m60EnergyDensity g (fun z => v (s, z)) p)
      0 0 ∧
    HasDerivAt (fun s => m64AnnulusArea g (fun z => v (s, z))) 0 0 := by
  let E := fun s => ∫ p in m64AnnulusDomain,
    m60EnergyDensity g (fun z => v (s, z)) p
  let a := fun s => m64AnnulusArea g (fun z => v (s, z))
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hmapzero : (fun z => v (0, z)) = A.map := funext hcenter
  have harea0 : a 0 = A.area := by simp only [a, hmapzero, M64Annulus.area]
  have henergy0 : E 0 = A.area := by
    simp only [E, hmapzero]
    exact m64Annulus_energy_eq_area_of_ae_conformal A hconformal
  have hint (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      IntegrableOn (m60EnergyDensity g (fun z => v (s, z)))
        m64AnnulusDomain volume := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    exact B.energy_integrable.congr (m64Annulus_energyDensity_ae_eq_of_eqOn g hB)
  have hcomparison (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      A.area ≤ a s ∧ a s ≤ E s := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    have hBarea : B.area = a s :=
      integral_congr_ae (m64Annulus_areaDensity_ae_eq_of_eqOn g hB)
    have hBenergy : (∫ p in m64AnnulusDomain, m60EnergyDensity g B.map p) = E s :=
      integral_congr_ae (m64Annulus_energyDensity_ae_eq_of_eqOn g hB)
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
  have hd := (m64AnnulusEnergy_hasDerivAt_of_supported_variation g hepsilon
    hO hK hKO hKdomain hv hfix hint).2
  have hE : HasDerivAt E 0 0 := by
    have hdE : DifferentiableAt ℝ E 0 := hd.differentiableAt
    simpa only [hlocal.deriv_eq_zero] using hdE.hasDerivAt
  refine ⟨hE, hasDerivAt_zero_of_squeezed_minimum hE
    (harea0.trans henergy0.symm) ?_ ?_⟩
  · filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    change a 0 ≤ a s
    rw [harea0]
    exact (hcomparison s hs).1
  · filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact (hcomparison s hs).2

/-- The global-map agreement form of supported annular stationarity. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Annulus_supported_stationarity_of_conformal_minimum
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {O K : Set LoopPlane} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hKdomain : K ⊆ m64AnnulusDomain)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hadmissible : ∀ s ∈ Ioo (-epsilon) epsilon,
      ∃ B : M64Annulus g c0 c1, B.map = fun p => v (s, p))
    (hcenter : ∀ p, v (0, p) = A.map p)
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∉ K,
      v (s, z) = v (0, z)) :
    HasDerivAt
      (fun s => ∫ p in m64AnnulusDomain, m60EnergyDensity g (fun z => v (s, z)) p)
      0 0 ∧
    HasDerivAt (fun s => m64AnnulusArea g (fun z => v (s, z))) 0 0 := by
  apply m64Annulus_supported_stationarity_of_conformal_minimum_of_eqOn
    A hminimum hconformal hepsilon hO hK hKO hKdomain hv ?_ hcenter hfix
  intro s hs
  obtain ⟨B, hB⟩ := hadmissible s hs
  exact ⟨B, fun p _ => congr_fun hB p⟩

end PoincareMT
