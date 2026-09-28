import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusDivergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapLocalFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64AnnulusEnergy_intrinsic_boundary_first_variation
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    {v : ℝ × LoopPlane → M}
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p) :
    HasDerivAt (fun r => ∫ p in m64AnnulusDomain,
      m60EnergyDensity g (fun z => v (r, z)) p)
      ((∫ s in Icc (0 : ℝ) 1,
          m64MovingAnnulusCurrent g v 0 (0, annulusPoint curvePeriod s) -
            m64MovingAnnulusCurrent g v 0 (0, annulusPoint 0 s)) +
        ∫ x in Icc (0 : ℝ) curvePeriod,
          m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 1) -
            m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 0)) 0 := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun p => v (q.1, p)) q.2
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
        fderiv ℝ (J 0) p (e 0) + fderiv ℝ (J 1) p (e 1) := by
    have hEp := m60EnergyDensity_family_contDiffAt g
      (hv.contMDiffAt (hopen.mem_nhds (show (0, p) ∈
        Ioo (-epsilon) epsilon ×ˢ U from ⟨hzero, hsub hp⟩)))
    have htime := (hEp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (l := E) (f := fun r : ℝ => (r, p)) 0
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 p))
    have hcoords : annulusPoint (p 0) (p 1) = p := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    have hdiv := m64MovingAnnulus_energyDensity_eq_current_divergence D A
      hminimum hconformal (hA.mono hsub) hopen hv hbase
      (x := p 0) (s := p 1)
      (by rw [hcoords]; exact ⟨hzero, hsub hp⟩) (by rw [hcoords]; exact hp)
    have htime' : fderiv ℝ E (0, p) (1, 0) =
        deriv (fun r => m60EnergyDensity g (fun z => v (r, z)) p) 0 := htime.deriv.symm
    exact htime'.trans (by simpa only [hcoords, J, e, EuclideanSpace.basisFun_apply] using hdiv)
  have hrestrict : volume.restrict (interior m64AnnulusDomain) =
      volume.restrict m64AnnulusInterior := by
    rw [← m64Annulus_restrict_closed_eq_interior]
    exact Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior
  have hintegral : (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) =
      (∫ p in interior m64AnnulusDomain, fderiv ℝ (J 0) p (e 0)) +
        ∫ p in interior m64AnnulusDomain, fderiv ℝ (J 1) p (e 1) := by
    rw [m64Annulus_restrict_closed_eq_interior, ← integral_add (hD 0) (hD 1)]
    apply integral_congr_ae
    rw [hrestrict]
    filter_upwards [ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet] with p hp
    exact hpoint p hp
  have hd := (m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation g hepsilon hU hdom hv).2
  change HasDerivAt (fun r => ∫ p in m64AnnulusDomain, E (r, p))
    (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 at hd
  rw [hintegral] at hd
  have hhor := m64Annulus_integral_horizontal_derivative_of_contDiffOn hU hdom (hJ 0)
  have hver := m64Annulus_integral_vertical_derivative_of_contDiffOn hU hdom (hJ 1)
  simpa only [e, EuclideanSpace.basisFun_apply, hhor, hver] using hd

end PoincareConjecture
