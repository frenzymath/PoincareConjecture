import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusMinimalLogBoundary
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusLogBoundaryLimit













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}





theorem m64Annulus_log_boundary_curvature_le_of_conformal_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ p ∈ m64AnnulusInterior, D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity g A.map (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity g A.map (annulusPoint x 1)) :
    -(1 / 2 : ℝ) *
      ((∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ (m60EnergyDensity g A.map) (annulusPoint x 1)
            (EuclideanSpace.single (1 : Fin 2) 1) /
          m60EnergyDensity g A.map (annulusPoint x 1)) -
        ∫ x in Icc (0 : ℝ) curvePeriod,
          fderiv ℝ (m60EnergyDensity g A.map) (annulusPoint x 0)
              (EuclideanSpace.single (1 : Fin 2) 1) /
            m60EnergyDensity g A.map (annulusPoint x 0)) ≤ K * A.area := by
  let E := m60EnergyDensity g A.map
  let b1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hE : ContDiffOn ℝ ∞ E O := m64EnergyDensity_contDiffOn hO hA
  have hlo := m64Annulus_log_normal_trace_tendsto hO hdom hE
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hlower
  have hhi := m64Annulus_log_normal_trace_tendsto hO hdom hE
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hupper
  have hbound : -2 * K * A.area ≤
      (∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 1) b1 /
        E (annulusPoint x 1)) -
      ∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 0) b1 /
        E (annulusPoint x 0) := by
    apply ge_of_tendsto (hhi.sub hlo)
    apply Eventually.of_forall
    intro m
    let eps : ℝ := 1 / ((m : ℝ) + 1)
    have heps : 0 < eps := by dsimp only [eps]; positivity
    let L := fun p => Real.log (E p + eps)
    have hL : ContDiffOn ℝ ∞ L O := by
      intro p hp
      exact (((hE.contDiffAt (hO.mem_nhds hp)).add contDiffAt_const).log
        (add_pos_of_nonneg_of_pos (m60EnergyDensity_nonneg g A.map p) heps).ne').contDiffWithinAt
    have hD : ContinuousOn (fun p => fderiv ℝ L p b1) O :=
      ((hL.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const).continuousOn
    have htrace (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        IntegrableOn (fun x => fderiv ℝ L (annulusPoint x s) b1)
          (Icc (0 : ℝ) curvePeriod) volume := by
      have hcurve : Continuous (fun x : ℝ => annulusPoint x s) := by
        unfold annulusPoint
        fun_prop
      apply (hD.comp hcurve.continuousOn ?_).integrableOn_compact isCompact_Icc
      intro x hx
      apply hdom
      change 0 ≤ x ∧ x ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
      exact ⟨hx.1, hx.2, hs⟩
    have hraw := m64Annulus_log_energy_boundary_lower_bound_of_conformal_minimum
      D A hminimum hconformal hO hdom hA hK heps hsec
    change -2 * K * A.area ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ L (annulusPoint x 1) b1 - fderiv ℝ L (annulusPoint x 0) b1 at hraw
    rw [integral_sub (htrace 1 (by simp)) (htrace 0 (by simp))] at hraw
    exact hraw
  change -(1 / 2 : ℝ) *
    ((∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 1) b1 /
      E (annulusPoint x 1)) -
    ∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ E (annulusPoint x 0) b1 /
      E (annulusPoint x 0)) ≤ K * A.area
  linarith

end PoincareConjecture
