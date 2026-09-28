import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ConformalMinimumStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SupportedChartAnnulusVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusChartEnergyVariation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}



theorem m64Annulus_chart_test_integral_eq_zero_of_conformal_minimum
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (b : M) {U : Set LoopPlane} (hU : IsOpen U)
    (hUinside : U ⊆ m64AnnulusInterior)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map U)
    (hfU : MapsTo A.map U (extChartAt (𝓡 n) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hcompact : HasCompactSupport V) (hsupport : tsupport V ⊆ U) :
    let u := (extChartAt (𝓡 n) b) ∘ A.map
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    (∫ z : LoopPlane, ∑ i : Fin 2, B (u z)
      (covDerivAlong (christoffelBilinear B) u V
        (EuclideanSpace.basisFun (Fin 2) ℝ i) z)
      (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = 0 := by
  let u := (extChartAt (𝓡 n) b) ∘ A.map
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let J := fun z => ∑ i : Fin 2,
    B (u z) (covDerivAlong (christoffelBilinear B) u V (e i) z)
      (fderiv ℝ u z (e i))
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  let v := M60.supportedChartVariation c U A.map V
  have hfU' : MapsTo A.map U c.source := by
    simpa only [c, extChartAt_source] using hfU
  obtain ⟨epsilon, hepsilon, hv, hchart, hadmissible⟩ :=
    m64SupportedChartVariation_exists_admissible_interval A b hU hUinside hf hfU'
      V hV hcompact hsupport
  have hcenter : ∀ p, v (0, p) = A.map p :=
    M60.supportedChartVariation_zero c U A.map V hfU'
  have hfixall (s : ℝ) (z : LoopPlane) (hz : z ∉ tsupport V) :
      v (s, z) = A.map z :=
    m64SupportedChartVariation_eq_of_notMem_tsupport A b hfU' V s hz
  have hfix (s : ℝ) (_hs : s ∈ Ioo (-epsilon) epsilon)
      (z : LoopPlane) (hz : z ∉ tsupport V) : v (s, z) = v (0, z) := by
    rw [hcenter]
    exact hfixall s z hz
  have hKdomain : tsupport V ⊆ m64AnnulusDomain :=
    (hsupport.trans hUinside).trans m64AnnulusInterior_subset_domain
  have hstat := (m64Annulus_supported_stationarity_of_conformal_minimum_of_eqOn
    A hminimum hconformal hepsilon hU hcompact hsupport hKdomain hv
      hadmissible hcenter hfix).1
  have hint (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      IntegrableOn (m60EnergyDensity g (fun z => v (s, z))) m64AnnulusDomain volume := by
    obtain ⟨C, hC⟩ := hadmissible s hs
    exact C.energy_integrable.congr (m64Annulus_energyDensity_ae_eq_of_eqOn g hC)
  have htotal := m64AnnulusEnergy_hasDerivAt_of_supported_variation g
    hepsilon hU hcompact hsupport hKdomain hv hfix hint
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun z => v (q.1, z)) q.2
  let D := fun q : ℝ × LoopPlane => E q - E (0, q.2)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∈ U,
      v (s, z) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, z)) =
          extChartAt (𝓡 n) b (A.map z) + s • V z := by
    simpa only [extChartAt_source, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp] using hchart
  have hDzero (s : ℝ) (z : LoopPlane) (hz : z ∉ tsupport V) : D (s, z) = 0 := by
    apply sub_eq_zero.mpr
    apply m60EnergyDensity_congr_of_eventuallyEq g
    filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hz] with y hy
    exact (hfixall s y hy).trans (hcenter y).symm
  have hderiv (z : LoopPlane) : fderiv ℝ D (0, z) (1, 0) = J z := by
    by_cases hz : z ∈ U
    · have hEp : ContDiffAt ℝ ∞ E (0, z) :=
        m60EnergyDensity_family_contDiffAt g
          (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨hzero, hz⟩))
      have hproj : ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => ((0 : ℝ), q.2))
          (0, z) := contDiffAt_const.prodMk contDiffAt_snd
      have hEcomp : ContDiffAt ℝ ∞ (fun q : ℝ × LoopPlane => E (0, q.2))
          (0, z) := ContDiffAt.comp (f := fun q : ℝ × LoopPlane => (0, q.2))
            (g := E) (0, z) hEp hproj
      have hDp : ContDiffAt ℝ ∞ D (0, z) := hEp.sub hEcomp
      have hpoint := m64EnergyDensity_hasDerivAt_of_affine_chart g b A.map hU
        hf hfU V hV hepsilon hv hcoord z hz
      exact ((hDp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        (l := D) (f := fun s : ℝ => (s, z)) 0
          ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z))).unique
            (hpoint.sub_const (E (0, z)))
    · have hout : z ∉ tsupport V := fun h => hz (hsupport h)
      have hJ : J z = 0 := by
        simp only [J, covDerivAlong, image_eq_zero_of_notMem_tsupport hout,
          fderiv_of_notMem_tsupport (𝕜 := ℝ) hout, zero_apply,
          map_zero, add_zero, Finset.sum_const_zero]
      have hDeq : D =ᶠ[𝓝 (0, z)] (fun _ => (0 : ℝ)) := by
        filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport V).isOpen_compl.mem_nhds hout)] with q hq
        exact hDzero q.1 q.2 hq
      simp only [hDeq.fderiv_eq, fderiv_const_apply, zero_apply, hJ]
  change (∫ z : LoopPlane, J z) = 0
  calc
    _ = ∫ z : LoopPlane, fderiv ℝ D (0, z) (1, 0) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (hderiv z).symm
    _ = 0 := htotal.2.unique hstat

end PoincareConjecture
