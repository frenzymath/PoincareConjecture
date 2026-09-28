import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.UnitRicciControl
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusProductMovingEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



theorem auxiliaryCircle_modulusEnergyRicci_abs_le_of_unit_bound
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    (t : ℝ) {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hunit : ∀ x : M, ∀ v : Fin 4 → TangentSpace (𝓡 n) x,
      (∀ i, (F.metric t).tangentNorm x (v i) ≤ 1) →
        |(F.connection t).curvatureTensor x (v 0) (v 1) (v 2) (v 3)| ≤ K)
    (f : LoopPlane → Q.charts.Point) (p : LoopPlane) :
    let d := mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) f p
    |r * (Q.flow.connection t).ricci (f p)
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
      r⁻¹ * (Q.flow.connection t).ricci (f p)
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (d (EuclideanSpace.basisFun (Fin 2) ℝ 1))| ≤
      2 * ((n : ℝ) - 1) * K * m64ModulusEnergyDensity (Q.flow.metric t) r f p := by
  let d := mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) f p
  let u := fun i : Fin 2 => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have h0 := mul_le_mul_of_nonneg_left
    (auxiliaryCircle_ricci_quadratic_abs_le_of_unit_bound P Q hn t hK (f p)
      (hunit (f p).1.1) (u 0)) hr.le
  have h1 := mul_le_mul_of_nonneg_left
    (auxiliaryCircle_ricci_quadratic_abs_le_of_unit_bound P Q hn t hK (f p)
      (hunit (f p).1.1) (u 1)) (inv_nonneg.mpr hr.le)
  calc
    _ ≤ |r * (Q.flow.connection t).ricci (f p) (u 0) (u 0)| +
        |r⁻¹ * (Q.flow.connection t).ricci (f p) (u 1) (u 1)| := abs_add_le _ _
    _ = r * |(Q.flow.connection t).ricci (f p) (u 0) (u 0)| +
        r⁻¹ * |(Q.flow.connection t).ricci (f p) (u 1) (u 1)| := by
      rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_pos (inv_pos.mpr hr)]
    _ ≤ r * (((n : ℝ) - 1) * K * (Q.flow.metric t).inner (f p) (u 0) (u 0)) +
        r⁻¹ * (((n : ℝ) - 1) * K * (Q.flow.metric t).inner (f p) (u 1) (u 1)) :=
      add_le_add h0 h1
    _ = _ := by
      simp only [m64ModulusEnergyDensity, m60AreaGram]
      change r * (((n : ℝ) - 1) * K * (Q.flow.metric t).inner (f p) (u 0) (u 0)) +
        r⁻¹ * (((n : ℝ) - 1) * K * (Q.flow.metric t).inner (f p) (u 1) (u 1)) =
        2 * ((n : ℝ) - 1) * K *
          ((r * (Q.flow.metric t).inner (f p) (u 0) (u 0) +
            r⁻¹ * (Q.flow.metric t).inner (f p) (u 1) (u 1)) / 2)
      ring



theorem auxiliaryCircle_annulus_modulusEnergy_derivative_le_of_ambient_bounds
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    {t : ℝ} (ht : t ∈ Ioo a b) {r : ℝ} (hr : 0 < r)
    {v : ℝ × LoopPlane → Q.charts.Point}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 ((n + 1) + 1)) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    {K0 K1 K2 : ℝ} (hK0 : 0 ≤ K0)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    let E := fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity (Q.flow.metric t) r (fun z => v (q.1, z)) q.2
    let H := fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity (Q.flow.metric (t + q.1)) r (fun z => v (q.1, z)) q.2
    (∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)) ≤
      (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) +
        2 * ((n : ℝ) - 1) * K0 * (∫ p in m64AnnulusDomain, E (0, p)) := by
  let E := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (Q.flow.metric t) r (fun z => v (q.1, z)) q.2
  let H := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (Q.flow.metric (t + q.1)) r (fun z => v (q.1, z)) q.2
  let C := 2 * ((n : ℝ) - 1) * K0
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hv0 (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 ((n + 1) + 1)) ∞ v (0, p) :=
    hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hzero, hdom hp⟩)
  have hE : ContDiffOn ℝ ∞ E (Ioo (-epsilon) epsilon ×ˢ U) := by
    intro q hq
    exact (m64ModulusEnergyDensity_family_contDiffAt (Q.flow.metric t) r
      (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds hq))).contDiffWithinAt
  have hint0 : IntegrableOn (fun p => E (0, p)) m64AnnulusDomain volume :=
    (hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hzero, hdom hp⟩)).integrableOn_compact m64AnnulusDomain_isCompact
  have hmap := m64ModulusAnnulusEnergy_hasDerivAt_of_local_smooth_variation
    (Q.flow.metric t) r hepsilon hU hdom hv
  have hflow := m64ModulusAnnulusEnergy_hasDerivAt_of_local_moving_metric
    Q.flow r ht hepsilon hU hdom hv
  have hpoint (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) :
      fderiv ℝ H (0, p) (1, 0) ≤ fderiv ℝ E (0, p) (1, 0) + C * E (0, p) := by
    have hEd := ((m64ModulusEnergyDensity_family_contDiffAt (Q.flow.metric t) r
      (hv0 p hp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        (l := E) (f := fun s : ℝ => (s, p)) 0
        ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p))
    have hHd := ((m64ModulusEnergyDensity_moving_metric_contDiffAt Q.flow r t
      (q := (0, p)) (by simpa only [add_zero] using ht) (hv0 p hp)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt
          (l := H) (f := fun s : ℝ => (s, p)) 0
          ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 p))
    have heq := hHd.unique
      (m64ModulusAnnulus_moving_metric_energy_hasDerivAt Q.flow r ht p (hv0 p hp))
    have hmapvalue : deriv (fun s => E (s, p)) 0 = fderiv ℝ E (0, p) (1, 0) := hEd.deriv
    change fderiv ℝ H (0, p) (1, 0) = deriv (fun s => E (s, p)) 0 - _ - _ at heq
    rw [hmapvalue] at heq
    have hric := auxiliaryCircle_modulusEnergyRicci_abs_le_of_unit_bound P Q hn t hr hK0
      (hBounds.riemann t (Ioo_subset_Icc_self ht)) (fun z => v (0, z)) p
    change abs _ ≤ C * E (0, p) at hric
    have hneg := neg_le_abs
      (r * (Q.flow.connection t).ricci (v (0, p))
        (mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) +
       r⁻¹ * (Q.flow.connection t).ricci (v (0, p))
        (mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) (fun z => v (0, z)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
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

end PoincareConjecture.M64
