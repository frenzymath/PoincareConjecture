import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusMinimalLogCurvature
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusEnergyPeriodicity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusLaplacianBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_log_energy_boundary_lower_bound_of_conformal_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -2 * K * A.area ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ (fun q => Real.log (m60EnergyDensity g A.map q + ε))
          (annulusPoint x 1) (EuclideanSpace.single (1 : Fin 2) 1) -
        fderiv ℝ (fun q => Real.log (m60EnergyDensity g A.map q + ε))
          (annulusPoint x 0) (EuclideanSpace.single (1 : Fin 2) 1) := by
  let E := m60EnergyDensity g A.map
  let L := fun q => Real.log (E q + ε)
  let b0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hE : ContDiffOn ℝ ∞ E O := m64EnergyDensity_contDiffOn hO hA
  have hL : ContDiffOn ℝ ∞ L O := by
    intro p hp
    exact (((hE.contDiffAt (hO.mem_nhds hp)).add contDiffAt_const).log
      (add_pos_of_nonneg_of_pos (m60EnergyDensity_nonneg g A.map p) hε).ne').contDiffWithinAt
  have hD (b : LoopPlane) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ L q b) O :=
    (hL.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hDD (b : LoopPlane) : IntegrableOn
      (fun p => fderiv ℝ (fun q => fderiv ℝ L q b) p b) m64AnnulusDomain volume :=
    (((hD b).fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn.mono hdom
        |>.integrableOn_compact m64AnnulusDomain_isCompact
  have hEI : IntegrableOn E m64AnnulusDomain volume :=
    (hE.continuousOn.mono hdom).integrableOn_compact m64AnnulusDomain_isCompact
  have hI : m64AnnulusInterior ⊆ O := m64AnnulusInterior_subset_domain.trans hdom
  have hmem : ∀ᵐ p ∂volume.restrict m64AnnulusDomain, p ∈ m64AnnulusInterior := by
    rw [Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior]
    exact ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet
  have hbound : (∫ p in m64AnnulusDomain, -2 * K * E p) ≤
      ∫ p in m64AnnulusDomain,
        fderiv ℝ (fun q => fderiv ℝ L q b0) p b0 +
          fderiv ℝ (fun q => fderiv ℝ L q b1) p b1 := by
    apply integral_mono_ae (hEI.const_mul (-2 * K)) ((hDD b0).add (hDD b1))
    filter_upwards [hmem] with p hp
    exact m64Annulus_log_energy_laplacian_lower_bound_of_conformal_minimum
      D A hminimum hconformal (hA.mono hI) hp hK hε (hsec p hp)
  have hseam (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      fderiv ℝ L (annulusPoint curvePeriod s) b0 = fderiv ℝ L (annulusPoint 0 s) b0 := by
    have hshift : annulusPoint curvePeriod 0 + annulusPoint 0 s =
        annulusPoint curvePeriod s := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    have hp : annulusPoint curvePeriod s ∈ m64AnnulusDomain := by
      change 0 ≤ curvePeriod ∧ curvePeriod ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
      exact ⟨by unfold curvePeriod; positivity, le_rfl, hs⟩
    have hperiod := m64Annulus_energy_transform_fderiv_periodic A
      (fun v => Real.log (v + ε)) (annulusPoint 0 s)
      (by rw [hshift]; exact hA.contMDiffAt (hO.mem_nhds (hdom hp)))
    rw [hshift] at hperiod
    exact congrArg (fun T : LoopPlane →L[ℝ] ℝ => T b0) hperiod
  have hboundary := m64Annulus_laplacian_integral_eq_boundary hO hdom hL hseam
  rw [integral_const_mul] at hbound
  change -2 * K * (∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p) ≤ _ at hbound
  rw [m64Annulus_energy_eq_area_of_ae_conformal A hconformal, hboundary] at hbound
  exact hbound

end PoincareConjecture
