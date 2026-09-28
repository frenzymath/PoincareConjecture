import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUEnergyRegularity
import PoincareConjecture.Proofs.M60.Mathlib.SUPlaneMapConstancy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60Sphere_constant_of_energyDensity_zero (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hzero : ∀ z : LoopPlane, m60SphereEnergyDensity g f z = 0) :
    ∃ c : M, ∀ p : UnitTwoSphere, f p = c := by
  let φ := f ∘ m60SphereParameter
  have hφ : MDifferentiable (𝓡 2) (𝓡 n) φ :=
    (hf.comp (m60SphereParameter_contMDiff.of_le (by simp))).mdifferentiable (by simp)
  have hd (z : LoopPlane) : mfderiv (𝓡 2) (𝓡 n) φ z = 0 := by
    have he := hzero z
    change (1 / 2 : ℝ) * Matrix.trace (m60AreaGram g φ z) = 0 at he
    rw [Matrix.trace_fin_two] at he
    have h0 := m60AreaGram_diagonal_nonneg g φ z 0
    have h1 := m60AreaGram_diagonal_nonneg g φ z 1
    have hb (i : Fin 2) : mfderiv (𝓡 2) (𝓡 n) φ z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 := by
      have hg : m60AreaGram g φ z i i = 0 := by
        fin_cases i
        · change m60AreaGram g φ z 0 0 = 0
          linarith
        · change m60AreaGram g φ z 1 1 = 0
          linarith
      by_contra hne
      have hp := g.pos (φ z) _ hne
      change 0 < m60AreaGram g φ z i i at hp
      linarith
    apply ContinuousLinearMap.ext
    intro w
    have heq := (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr w
    rw [← heq, map_sum]
    simp only [map_smul, hb, smul_zero, Finset.sum_const_zero, zero_apply]
  have hc (z : LoopPlane) : φ z = φ 0 := M60.plane_map_eq_of_mfderiv_zero hφ hd z 0
  refine ⟨φ 0, ?_⟩
  have hoff : EqOn f (fun _ => φ 0) ({m60SpherePole}ᶜ : Set UnitTwoSphere) := by
    intro p hp
    have hps : p ∈ m60SphereChart.source := by simpa [m60SphereChart] using hp
    have hpz : m60SphereParameter (m60SphereChart p) = p := m60SphereChart.left_inv hps
    simpa only [φ, Function.comp_apply, hpz] using hc (m60SphereChart p)
  have hclosed := hoff.closure hf.continuous continuous_const
  have hdense : Dense ({m60SpherePole}ᶜ : Set UnitTwoSphere) :=
    M60.dense_compl_singleton_of_charted (H := LoopPlane) m60SpherePole
  exact fun p => hclosed (hdense p)

variable [SecondCountableTopology M] [CompactSpace M]

theorem m60HarmonicSphere_uniform_energy_gap (g : RiemannianMetric n M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (f : UnitTwoSphere → M),
      ContMDiff (𝓡 2) (𝓡 n) ∞ f → M60SphereChartHarmonic g f →
      (∃ p q : UnitTwoSphere, f p ≠ f q) → ε < m60SphereEnergy g f := by
  obtain ⟨ε, hε, hzero⟩ := m60HarmonicSphere_small_energy_density_zero g
  refine ⟨ε, hε, fun f hf hharm hnonconst => ?_⟩
  by_contra hle
  obtain ⟨c, hc⟩ := m60Sphere_constant_of_energyDensity_zero g f (hf.of_le (by simp))
    (hzero f hf hharm (le_of_not_gt hle))
  obtain ⟨p, q, hpq⟩ := hnonconst
  exact hpq ((hc p).trans (hc q).symm)

end PoincareConjecture
