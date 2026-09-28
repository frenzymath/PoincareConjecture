import PoincareConjecture.Proofs.M36.CylinderChartMetric
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Definitions.M60MinimalSpheres

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m60SphereChart_eq_chartAt :
    m60SphereChart = chartAt LoopPlane (-m60SpherePole) := by
  let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
  change stereographic' 2 m60SpherePole = stereographic' 2 (-(-m60SpherePole))
  rw [neg_neg]

theorem m60SphereParameter_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ m60SphereParameter := by
  have ht : (chartAt LoopPlane (-m60SpherePole)).target = Set.univ := by
    let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
    change (stereographic' 2 (-(-m60SpherePole))).target = Set.univ
    simp
  rw [m60SphereParameter, m60SphereChart_eq_chartAt]
  exact contMDiffOn_univ.mp (ht ▸ contMDiffOn_chart_symm (I := 𝓡 2))

theorem m60SphereParameter_inner (z v w : LoopPlane) :
    m60RoundSphereInner (m60SphereParameter z)
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z v)
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z w) =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * inner ℝ v w := by
  unfold m60RoundSphereInner m60SphereParameter
  rw [m60SphereChart_eq_chartAt]
  exact M36.sphere_chart_differential_inner_at (-m60SpherePole) z v w

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AreaGram_of_weaklyConformal (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hc : M60WeaklyConformal g f) (z : LoopPlane) :
    ∃ scale : ℝ, 0 ≤ scale ∧ ∀ i j : Fin 2,
      m60AreaGram g (f ∘ m60SphereParameter) z i j =
        scale * (16 / (‖z‖ ^ 2 + 4) ^ 2) *
          inner ℝ (EuclideanSpace.basisFun (Fin 2) ℝ i)
            (EuclideanSpace.basisFun (Fin 2) ℝ j) := by
  obtain ⟨scale, hscale, hinner⟩ := hc (m60SphereParameter z)
  refine ⟨scale, hscale, ?_⟩
  intro i j
  unfold m60AreaGram
  rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
    (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
  change g.inner _ (mfderiv (𝓡 2) (𝓡 n) f _
    (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z _))
    (mfderiv (𝓡 2) (𝓡 n) f _
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z _)) = _
  rw [hinner, m60SphereParameter_inner, mul_assoc]

theorem m60SphereDensity_eq_of_weaklyConformal (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hc : M60WeaklyConformal g f) (z : LoopPlane) :
    m60SphereAreaDensity g f z = m60SphereEnergyDensity g f z := by
  obtain ⟨scale, -, hgram⟩ := m60AreaGram_of_weaklyConformal g f hf hc z
  apply m60AreaDensity_eq_energyDensity_of_gram
  · rw [hgram, hgram]
    simp
  · rw [hgram]
    simp [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]

theorem m60SphereArea_eq_energy_of_weaklyConformal (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hc : M60WeaklyConformal g f) : m60SphereArea g f = m60SphereEnergy g f := by
  unfold m60SphereArea m60SphereEnergy
  congr 1
  funext z
  exact m60SphereDensity_eq_of_weaklyConformal g f hf hc z

end PoincareConjecture
