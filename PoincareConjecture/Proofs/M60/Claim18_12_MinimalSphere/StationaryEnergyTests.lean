import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.SupportedSphereVariation
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.SupportedEnergyDerivative
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ChartEnergyFirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60EnergyStationary_test_integral_eq_zero (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hstat : M60EnergyStationary g f) (b : M)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hcompact : HasCompactSupport V)
    (hsupport : tsupport V ⊆ (f ∘ m60SphereParameter) ⁻¹' (extChartAt (𝓡 n) b).source) :
    let u := (extChartAt (𝓡 n) b) ∘ (f ∘ m60SphereParameter)
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    (∫ z : LoopPlane, ∑ i : Fin 2, B (u z)
      (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) z)
      (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i))) = 0 := by
  let u := (extChartAt (𝓡 n) b) ∘ (f ∘ m60SphereParameter)
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let J := fun z => ∑ i : Fin 2,
    B (u z) (covDerivAlong (christoffelBilinear B) u V (e i) z) (fderiv ℝ u z (e i))
  let v := m60SupportedSphereVariation b f V
  obtain ⟨ε, hε, hv, hchart⟩ := m60SupportedSphereVariation_exists_interval b f hf V hV
    hcompact (fun z hz => by
      simpa only [extChartAt_source, mem_preimage, Function.comp_apply] using hsupport hz)
  have hv0 : ∀ p, v (0, p) = f p := m60SupportedSphereVariation_zero b f V
  have hfix (s : ℝ) (_hs : s ∈ Ioo (-ε) ε) (z : LoopPlane) (hz : z ∉ tsupport V) :
      v (s, m60SphereParameter z) = v (0, m60SphereParameter z) := by
    rw [hv0]
    exact m60SupportedSphereVariation_eq_of_notMem_tsupport b f V s hz
  let E := fun q : ℝ × LoopPlane => m60SphereEnergyDensity g (fun p => v (q.1, p)) q.2
  have hE : ContDiffOn ℝ ∞ E (Ioo (-ε) ε ×ˢ (univ : Set LoopPlane)) :=
    m60SphereEnergyDensity_family_contDiffOn g hv
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hcoord : ∀ s ∈ Ioo (-ε) ε, ∀ z : LoopPlane,
      f (m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source →
        v (s, m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source ∧
          extChartAt (𝓡 n) b (v (s, m60SphereParameter z)) =
            extChartAt (𝓡 n) b (f (m60SphereParameter z)) + s • V z := by
    simpa only [v, extChartAt_source, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp] using hchart
  have hpoint (z : LoopPlane) :
      HasDerivAt (fun s => m60SphereEnergyDensity g (fun p => v (s, p)) z) (J z) 0 := by
    by_cases hz : f (m60SphereParameter z) ∈ (extChartAt (𝓡 n) b).source
    · exact m60SphereEnergyDensity_hasDerivAt_of_affine_chart g b f hf V hV hε hv hcoord z hz
    · have hout : z ∉ tsupport V := fun hzV => hz (hsupport hzV)
      have hJ : J z = 0 := by
        simp only [J, covDerivAlong, image_eq_zero_of_notMem_tsupport hout,
          fderiv_of_notMem_tsupport (𝕜 := ℝ) hout, zero_apply,
          map_zero, add_zero, Finset.sum_const_zero]
      rw [hJ]
      apply (hasDerivAt_const (0 : ℝ) (m60SphereEnergyDensity g f z)).congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro s
      apply m60EnergyDensity_congr_of_eventuallyEq g
      filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hout] with y hy
      exact m60SupportedSphereVariation_eq_of_notMem_tsupport b f V s hy
  have hderiv (z : LoopPlane) : fderiv ℝ E (0, z) (1, 0) = J z := by
    have hEp : ContDiffAt ℝ ∞ E (0, z) := hE.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hzero, mem_univ z⟩)
    have ht : HasDerivAt (fun s : ℝ => (s, z)) (1, 0) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
    exact ((hEp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (l := E) (f := fun s : ℝ => (s, z)) 0 ht).unique (hpoint z)
  have htotal := m60SphereEnergy_hasDerivAt_of_supported_variation g (v := v) hε hv
    hcompact hfix
  have hzeroIntegral := htotal.2.unique (hstat ε hε v hv hv0)
  change (∫ z : LoopPlane, J z) = 0
  calc
    (∫ z : LoopPlane, J z) = ∫ z : LoopPlane, fderiv ℝ E (0, z) (1, 0) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => (hderiv z).symm)
    _ = 0 := hzeroIntegral

end PoincareConjecture
