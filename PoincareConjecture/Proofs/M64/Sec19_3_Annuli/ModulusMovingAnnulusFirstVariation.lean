import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMovingAnnulusDivergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusProductMovingEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusPeriodicVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64ModulusAnnulusEnergy_intrinsic_boundary_first_variation
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    {v : ℝ × LoopPlane → M}
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p) :
    HasDerivAt (fun t => ∫ p in m64AnnulusDomain,
      m64ModulusEnergyDensity g r (fun z => v (t, z)) p)
      (r * (∫ s in Icc (0 : ℝ) 1,
          m64MovingAnnulusCurrent g v 0 (0, annulusPoint curvePeriod s) -
            m64MovingAnnulusCurrent g v 0 (0, annulusPoint 0 s)) +
        r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
          m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 1) -
            m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 0)) 0 := by
  let E := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity g r (fun p => v (q.1, p)) q.2
  let J := fun i p => m64MovingAnnulusCurrent g v i (0, p)
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hopen : IsOpen (Ioo (-epsilon) epsilon ×ˢ U) := isOpen_Ioo.prod hU
  have hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map U := by
    have hslice : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (fun p => v (0, p)) U :=
      hv.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
        (fun _ hp => ⟨hzero, hp⟩)
    exact (funext hbase) ▸ hslice
  have hJ (i : Fin 2) : ContDiffOn ℝ ∞ (J i) U := by
    intro p hp
    exact ((m64MovingAnnulusCurrent_contDiffAt g
      (hv.contMDiffAt (hopen.mem_nhds ⟨hzero, hp⟩)) i).comp p
        (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hD (i : Fin 2) : IntegrableOn (fun p => fderiv ℝ (J i) p (e i))
      (interior m64AnnulusDomain) volume :=
    ((((hJ i).fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
      contDiffOn_const).continuousOn.mono hdom).integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hsub : m64AnnulusInterior ⊆ U := m64AnnulusInterior_subset_domain.trans hdom
  have hpoint (p : LoopPlane) (hp : p ∈ m64AnnulusInterior) :
      fderiv ℝ E (0, p) (1, 0) =
        r * fderiv ℝ (J 0) p (e 0) + r⁻¹ * fderiv ℝ (J 1) p (e 1) := by
    have hEp := m64ModulusEnergyDensity_family_contDiffAt g r
      (hv.contMDiffAt (hopen.mem_nhds (show (0, p) ∈
        Ioo (-epsilon) epsilon ×ˢ U from ⟨hzero, hsub hp⟩)))
    have htime := (hEp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (l := E) (f := fun t : ℝ => (t, p)) 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 p))
    have hcoords : annulusPoint (p 0) (p 1) = p := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    have hdiv := m64MovingAnnulus_modulusEnergyDensity_eq_current_divergence D A hr
      hminimum hconformal (hA.mono hsub) hopen hv hbase
      (x := p 0) (s := p 1)
      (by rw [hcoords]; exact ⟨hzero, hsub hp⟩) (by rw [hcoords]; exact hp)
    have htime' : fderiv ℝ E (0, p) (1, 0) =
        deriv (fun t => m64ModulusEnergyDensity g r (fun z => v (t, z)) p) 0 :=
      htime.deriv.symm
    exact htime'.trans (by simpa only [hcoords, J, e, EuclideanSpace.basisFun_apply] using hdiv)
  have hrestrict : volume.restrict (interior m64AnnulusDomain) =
      volume.restrict m64AnnulusInterior := by
    rw [← m64Annulus_restrict_closed_eq_interior]
    exact Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior
  have hintegral : (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) =
      r * (∫ p in interior m64AnnulusDomain, fderiv ℝ (J 0) p (e 0)) +
        r⁻¹ * ∫ p in interior m64AnnulusDomain, fderiv ℝ (J 1) p (e 1) := by
    rw [m64Annulus_restrict_closed_eq_interior, ← integral_const_mul,
      ← integral_const_mul, ← integral_add ((hD 0).const_mul r) ((hD 1).const_mul r⁻¹)]
    apply integral_congr_ae
    rw [hrestrict]
    filter_upwards [ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet] with p hp
    exact hpoint p hp
  have hd := (m64ModulusAnnulusEnergy_hasDerivAt_of_local_smooth_variation
    g r hepsilon hU hdom hv).2
  change HasDerivAt (fun t => ∫ p in m64AnnulusDomain, E (t, p))
    (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 at hd
  rw [hintegral] at hd
  have hhor := m64Annulus_integral_horizontal_derivative_of_contDiffOn hU hdom (hJ 0)
  have hver := m64Annulus_integral_vertical_derivative_of_contDiffOn hU hdom (hJ 1)
  simpa only [e, EuclideanSpace.basisFun_apply, hhor, hver] using hd

theorem m64Annulus_periodic_first_variation_of_modulus_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    {v : ℝ × LoopPlane → M}
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hperiodic : ∀ t x s, v (t, annulusPoint (x + curvePeriod) s) =
      v (t, annulusPoint x s)) :
    HasDerivAt (fun t => ∫ p in m64AnnulusDomain,
      m64ModulusEnergyDensity g r (fun z => v (t, z)) p)
      (r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
        m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 1) -
          m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 0)) 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hseam : (∫ s in Icc (0 : ℝ) 1,
      m64MovingAnnulusCurrent g v 0 (0, annulusPoint curvePeriod s) -
        m64MovingAnnulusCurrent g v 0 (0, annulusPoint 0 s)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hp : annulusPoint curvePeriod s ∈ m64AnnulusDomain := by
      change 0 ≤ curvePeriod ∧ curvePeriod ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
      exact ⟨by unfold curvePeriod; positivity, le_rfl, hs⟩
    have hmd := (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
      (show (0, annulusPoint curvePeriod s) ∈ Ioo (-epsilon) epsilon ×ˢ U from
        ⟨hzero, hdom hp⟩))).mdifferentiableAt (by simp)
    have heq := m64MovingAnnulusCurrent_periodic g hperiodic 0 0 s
      (by simpa only [zero_add] using hmd) 0
    simp only [zero_add] at heq
    exact sub_eq_zero.mpr heq
  have hd := m64ModulusAnnulusEnergy_intrinsic_boundary_first_variation D A hr
    hminimum hconformal hepsilon hU hdom hv hbase
  simpa only [hseam, mul_zero, zero_add] using hd

end PoincareConjecture
