import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusSmoothGram
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusConformalLogCurvature
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ConformalMinimumHarmonic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_log_energy_laplacian_lower_bound_of_conformal_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {p : LoopPlane} (hp : p ∈ m64AnnulusInterior) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε)
    (hsec : D.sectionalCurvature (A.map p)
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
      (mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K) :
    -2 * K * m60EnergyDensity g A.map p ≤
      fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (m60EnergyDensity g A.map r + ε)) q
          (EuclideanSpace.single (0 : Fin 2) 1)) p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (m60EnergyDensity g A.map r + ε)) q
          (EuclideanSpace.single (1 : Fin 2) 1)) p
            (EuclideanSpace.single (1 : Fin 2) 1) := by
  let b := A.map p
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hpoint := m64Annulus_conformal_on_interior_of_ae A hA hconformal
  have hAp := hA.contMDiffAt (isOpen_m64AnnulusInterior.mem_nhds hp)
  have hchart : ∀ᶠ q in 𝓝 p, A.map q ∈ (extChartAt (𝓡 n) b).source :=
    hAp.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source b).mem_nhds (mem_extChartAt_source b))
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (isOpen_m64AnnulusInterior.mem_nhds hp) hchart)
  have hUI : U ⊆ m64AnnulusInterior := fun q hq => (hUsub hq).1
  have hUchart : MapsTo A.map U (extChartAt (𝓡 n) b).source :=
    fun q hq => (hUsub hq).2
  have hharm := m64Annulus_chart_harmonic_of_conformal_minimum A hminimum hconformal
    b hU hUI (hA.mono hUI) hUchart
  have henergy (q : LoopPlane) (hq : q ∈ U) :
      m60EnergyDensity g A.map q = m60AreaGram g A.map q 0 0 := by
    rw [m60EnergyDensity, Matrix.trace_fin_two, ← (hpoint q (hUI hq)).1]
    ring
  have hdd (q : LoopPlane) (hq : q ∈ U) :
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q e0)
        (mfderiv (𝓡 2) (𝓡 n) A.map q e0) = m60EnergyDensity g A.map q := by
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using (henergy q hq).symm
  have hee (q : LoopPlane) (hq : q ∈ U) :
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q e1)
        (mfderiv (𝓡 2) (𝓡 n) A.map q e1) = m60EnergyDensity g A.map q := by
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using
      ((hpoint q (hUI hq)).1.symm.trans (henergy q hq).symm)
  have hde (q : LoopPlane) (hq : q ∈ U) :
      g.inner (A.map q) (mfderiv (𝓡 2) (𝓡 n) A.map q e0)
        (mfderiv (𝓡 2) (𝓡 n) A.map q e1) = 0 := by
    simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using (hpoint q (hUI hq)).2
  apply m64ConformalHarmonicChart_log_add_laplacian_lower_bound D b hU hpU
    (hA.mono hUI) (fun q hq => hUchart hq) ?_ hdd hee hde hK hε hsec
  simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply] using hharm

end PoincareConjecture
