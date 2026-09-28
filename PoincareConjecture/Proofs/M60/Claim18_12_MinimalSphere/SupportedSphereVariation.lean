import PoincareConjecture.Proofs.M60.Mathlib.SupportedChartExtension
import PoincareConjecture.Proofs.M60.Mathlib.SupportedChartVariation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.StereographicConformal










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]



noncomputable def m60SupportedSphereVariation (b : M) (f : UnitTwoSphere → M)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) : ℝ × UnitTwoSphere → M :=
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  M60.supportedChartVariation c (f ⁻¹' c.source) f
    (M60.supportedChartExtension m60SphereChart V)



theorem m60SphereDisplacement_parameter (V : LoopPlane → EuclideanSpace ℝ (Fin n))
    (z : LoopPlane) :
    M60.supportedChartExtension m60SphereChart V (m60SphereParameter z) = V z := by
  have hz : z ∈ m60SphereChart.target := by simp [m60SphereChart]
  change M60.supportedChartExtension m60SphereChart V (m60SphereChart.symm z) = V z
  rw [M60.supportedChartExtension_of_mem m60SphereChart V (m60SphereChart.map_target hz)]
  exact congrArg V (m60SphereChart.right_inv hz)



theorem m60SupportedSphereVariation_zero (b : M) (f : UnitTwoSphere → M)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (p : UnitTwoSphere) :
    m60SupportedSphereVariation b f V (0, p) = f p :=
  M60.supportedChartVariation_zero _ _ f _ (fun _ hp => hp) p



theorem m60SupportedSphereVariation_parameter (b : M) (f : UnitTwoSphere → M)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (s : ℝ) (z : LoopPlane)
    (hz : f (m60SphereParameter z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source) :
    m60SupportedSphereVariation b f V (s, m60SphereParameter z) =
      (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
        (chartAt (EuclideanSpace ℝ (Fin n)) b (f (m60SphereParameter z)) + s • V z) := by
  rw [m60SupportedSphereVariation, M60.supportedChartVariation_of_mem _ _ f _ s hz,
    m60SphereDisplacement_parameter]



theorem m60SupportedSphereVariation_eq_of_notMem_tsupport (b : M)
    (f : UnitTwoSphere → M) (V : LoopPlane → EuclideanSpace ℝ (Fin n))
    (s : ℝ) {z : LoopPlane} (hz : z ∉ tsupport V) :
    m60SupportedSphereVariation b f V (s, m60SphereParameter z) = f (m60SphereParameter z) := by
  exact M40.chartPerturb_eq_of_zero (chartAt (EuclideanSpace ℝ (Fin n)) b)
    (Prod.snd ⁻¹' (f ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) b).source)) (f ∘ Prod.snd)
    (fun q : ℝ × UnitTwoSphere => q.1 • M60.supportedChartExtension m60SphereChart V q.2)
    (fun _ hp => hp) (by
      change s • M60.supportedChartExtension m60SphereChart V (m60SphereParameter z) = 0
      rw [m60SphereDisplacement_parameter, image_eq_zero_of_notMem_tsupport hz, smul_zero])

variable [IsManifold (𝓡 n) ∞ M]




theorem m60SupportedSphereVariation_exists_interval (b : M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hcompact : HasCompactSupport V)
    (hsupport : ∀ z ∈ tsupport V,
      f (m60SphereParameter z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source) :
    ∃ ε : ℝ, 0 < ε ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (m60SupportedSphereVariation b f V)
        (Ioo (-ε) ε ×ˢ (univ : Set UnitTwoSphere)) ∧
      ∀ s ∈ Ioo (-ε) ε, ∀ z : LoopPlane,
        f (m60SphereParameter z) ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source →
        m60SupportedSphereVariation b f V (s, m60SphereParameter z) ∈
            (chartAt (EuclideanSpace ℝ (Fin n)) b).source ∧
          chartAt (EuclideanSpace ℝ (Fin n)) b
            (m60SupportedSphereVariation b f V (s, m60SphereParameter z)) =
              chartAt (EuclideanSpace ℝ (Fin n)) b (f (m60SphereParameter z)) + s • V z := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  let W := M60.supportedChartExtension m60SphereChart V
  let U := f ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have htarget : tsupport V ⊆ m60SphereChart.target := by simp [m60SphereChart]
  have hchart : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m60SphereChart m60SphereChart.source := by
    rw [m60SphereChart_eq_chartAt]
    exact contMDiffOn_chart
  have hW := M60.contMDiff_supportedChartExtension m60SphereChart hchart hV hcompact htarget
  have hWcompact := M60.hasCompactSupport_supportedChartExtension m60SphereChart hcompact htarget
  have hWsupport : tsupport W ⊆ U := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := M60.tsupport_supportedChartExtension_subset
      m60SphereChart hcompact htarget hp
    exact hsupport z hz
  obtain ⟨ε, hε, hrange⟩ := M60.exists_supportedChartVariation_interval c hU
    hf.continuous.continuousOn hW.continuous hWcompact hWsupport (fun _ hp => hp)
  refine ⟨ε, hε, M60.contMDiffOn_supportedChartVariation c hU hf hW
    contMDiffOn_chart contMDiffOn_chart_symm hWsupport (fun _ hp => hp) hrange, ?_⟩
  intro s hs z hz
  rw [m60SupportedSphereVariation_parameter b f V s z hz]
  have hr : c (f (m60SphereParameter z)) + s • V z ∈ c.target := by
    simpa only [W, m60SphereDisplacement_parameter] using hrange s hs (m60SphereParameter z) hz
  exact ⟨c.map_target hr, c.right_inv hr⟩

end PoincareConjecture
