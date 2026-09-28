import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUHopfVanishing
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUConformalPole
import PoincareConjecture.Proofs.M60.Mathlib.SUGramConformal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60WeaklyConformal_of_chartHarmonic (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) : M60WeaklyConformal g f := by
  apply m60WeaklyConformal_of_compl_singleton g f hf m60SpherePole
  intro p hp
  have hps : p ∈ m60SphereChart.source := by simpa [m60SphereChart] using hp
  let z := m60SphereChart p
  have hpz : m60SphereParameter z = p := m60SphereChart.left_inv hps
  suffices ∃ s : ℝ, 0 ≤ s ∧ ∀ v w : TangentSpace (𝓡 2) (m60SphereParameter z),
      g.inner (f (m60SphereParameter z)) (mfderiv (𝓡 2) (𝓡 n) f (m60SphereParameter z) v)
        (mfderiv (𝓡 2) (𝓡 n) f (m60SphereParameter z) w) =
          s * m60RoundSphereInner (m60SphereParameter z) v w by
    exact hpz ▸ this
  let φ := f ∘ m60SphereParameter
  let B := M60.metricPullbackForm (n := 2) g φ z
  let a := m60AreaGram g φ z 0 0
  let σ : ℝ := 16 / (‖z‖ ^ 2 + 4) ^ 2
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have ha : 0 ≤ a := m60AreaGram_diagonal_nonneg g φ z 0
  refine ⟨a / σ, div_nonneg ha hσ.le, ?_⟩
  intro v w
  let d := mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z
  have hd := m60SphereParameter_mfderiv_isInvertible z
  have hgram := m60SphereGram_conformal_of_harmonic g f hf hharm z
  have hpair := M60.bilinear_eq_inner_of_conformal_gram B
    (fun _ _ => g.symm _ _ _) hgram.1 hgram.2 (d.inverse v) (d.inverse w)
  dsimp only [B] at hpair
  erw [M60.metricPullbackForm_apply, mfderiv_comp z
    ((hf _).mdifferentiableAt (by simp))
    ((m60SphereParameter_contMDiff z).mdifferentiableAt (by simp))] at hpair
  change g.inner _ (mfderiv (𝓡 2) (𝓡 n) f _ (d (d.inverse v)))
    (mfderiv (𝓡 2) (𝓡 n) f _ (d (d.inverse w))) =
      a * @inner ℝ LoopPlane _ (d.inverse v) (d.inverse w) at hpair
  rw [hd.self_apply_inverse, hd.self_apply_inverse] at hpair
  have hround := m60SphereParameter_inner z (d.inverse v) (d.inverse w)
  change m60RoundSphereInner _ (d (d.inverse v)) (d (d.inverse w)) =
    σ * @inner ℝ LoopPlane _ (d.inverse v) (d.inverse w) at hround
  rw [hd.self_apply_inverse, hd.self_apply_inverse] at hround
  rw [hpair, hround]
  field_simp

end PoincareConjecture
