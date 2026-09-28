import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMetricIntegral
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductEnergyRicciBound












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}






theorem m64CircleProduct_annulus_energy_derivative_le
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n)
    {t : ℝ} (ht : t ∈ Ioo a b)
    {v : ℝ × LoopPlane → P.charts.Point}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 (n + 1)) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity (P.flow.metric t) (fun z => v (q.1, z)) q.2
    let H := fun q : ℝ × LoopPlane =>
      m60EnergyDensity (P.flow.metric (t + q.1)) (fun z => v (q.1, z)) q.2
    (∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)) ≤
      (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) +
        2 * ((n : ℝ) - 1) * K * (∫ p in m64AnnulusDomain, E (0, p)) := by
  let E := fun q : ℝ × LoopPlane =>
    m60EnergyDensity (P.flow.metric t) (fun z => v (q.1, z)) q.2
  let H := fun q : ℝ × LoopPlane =>
    m60EnergyDensity (P.flow.metric (t + q.1)) (fun z => v (q.1, z)) q.2
  let C := 2 * ((n : ℝ) - 1) * K
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hv0 (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 (n + 1)) ∞ v (0, p) :=
    hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hzero, hdom hp⟩)
  have hE : ContDiffOn ℝ ∞ E (Ioo (-epsilon) epsilon ×ˢ U) := by
    intro q hq
    exact (m60EnergyDensity_family_contDiffAt (P.flow.metric t)
      (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds hq))).contDiffWithinAt
  have hint0 : IntegrableOn (fun p => E (0, p)) m64AnnulusDomain volume :=
    (hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hzero, hdom hp⟩)).integrableOn_compact m64AnnulusDomain_isCompact
  have hmap := m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation
    (P.flow.metric t) hepsilon hU hdom hv
  have hflow := m64AnnulusEnergy_hasDerivAt_of_local_moving_metric
    P.flow ht hepsilon hU hdom hv
  have hpoint (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      fderiv ℝ H (0, p) (1, 0) ≤ fderiv ℝ E (0, p) (1, 0) + C * E (0, p) := by
    have hEd := ((m60EnergyDensity_family_contDiffAt (P.flow.metric t)
      (hv0 p hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        (l := E) (f := fun r : ℝ => (r, p)) 0
        ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p))
    have hHd := ((m64Annulus_moving_metric_energy_contDiffAt P.flow t
      (q := (0, p)) (by simpa only [add_zero] using ht) (hv0 p hp)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt
          (l := H) (f := fun r : ℝ => (r, p)) 0
          ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p))
    have hformula := m64Annulus_moving_metric_energy_hasDerivAt P.flow ht p (hv0 p hp)
    have heq := hHd.unique hformula
    have hmapvalue : deriv (fun r => E (r, p)) 0 = fderiv ℝ E (0, p) (1, 0) :=
      hEd.deriv
    change fderiv ℝ H (0, p) (1, 0) = deriv (fun r => E (r, p)) 0 - _ - _ at heq
    rw [hmapvalue] at heq
    have hric := m64CircleProduct_energyRicci_abs_le P hn t hK hcurv
      (fun z => v (0, z)) p
    have hneg := neg_le_abs
      ((P.flow.connection t).ricci (v (0, p))
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
       (P.flow.connection t).ricci (v (0, p))
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
    change abs _ ≤ C * E (0, p) at hric
    linarith
  have hbound := integral_mono_ae hflow.1 (hmap.1.add (hint0.const_mul C))
    (show ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      fderiv ℝ H (0, p) (1, 0) ≤ fderiv ℝ E (0, p) (1, 0) + C * E (0, p) from by
        filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp
        exact hpoint p hp)
  change (∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)) ≤
    ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0) + C * E (0, p) at hbound
  rw [integral_add hmap.1 (hint0.const_mul C), integral_const_mul] at hbound
  exact hbound

end PoincareConjecture
