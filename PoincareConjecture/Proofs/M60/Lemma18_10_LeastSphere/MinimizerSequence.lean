import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSmoothCompetitors
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerPerturbedLimit











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M]




theorem m60PerturbedMinimizers_area_energy_tendsto (g : RiemannianMetric n M)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (ha : Tendsto alpha atTop (𝓝 1)) (ha1 : ∀ j, 1 ≤ alpha j)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hmin : ∀ j (h : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ h →
      ¬ IsNullHomotopicSphere h →
      m60SphereAlphaEnergy g (alpha j) (f j) ≤ m60SphereAlphaEnergy g (alpha j) h) :
    let I := sInf (m60SphereArea g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h})
    Tendsto (fun j => (m60SphereAlphaEnergy g (alpha j) (f j) - 4 * Real.pi) / 2)
      atTop (𝓝 I) ∧
      Tendsto (fun j => m60SphereEnergy g (f j)) atTop (𝓝 I) ∧
      Tendsto (fun j => m60SphereArea g (f j)) atTop (𝓝 I) := by
  let S : Set (UnitTwoSphere → M) :=
    {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}
  let I := sInf (m60SphereArea g '' S)
  have hI : I = sInf (m60SphereEnergy g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) ∞ h ∧ ¬ IsNullHomotopicSphere h}) :=
    m60SphereArea_smooth_energy_infimum g
  have ht := m60PerturbedMinimizers_energy_tendsto g alpha f ha ha1 hf hn hmin
  dsimp only at ht
  rw [← hI] at ht
  refine ⟨ht.1, ht.2, ?_⟩
  have hb : BddBelow (m60SphereArea g '' S) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, -, rfl⟩
    exact m60SphereArea_nonneg g h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht.2
  · intro j
    exact csInf_le hb ⟨f j, ⟨(hf j).of_le (by simp), hn j⟩, rfl⟩
  · intro j
    exact m60SphereArea_le_energy_of_integrable g (f j)
      (m60SphereEnergyDensity_integrable g (f j) ((hf j).of_le (by simp)))

namespace M60



theorem suAlphaSequence {eps0 : ℝ} (heps0 : 0 < eps0) :
    (∀ j : ℕ, 1 + eps0 / ((j : ℝ) + 2) ∈ Ioo 1 (1 + eps0)) ∧
      Tendsto (fun j : ℕ => 1 + eps0 / ((j : ℝ) + 2)) atTop (𝓝 1) := by
  constructor
  · intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    constructor
    · have : 0 < eps0 / ((j : ℝ) + 2) := div_pos heps0 (by positivity)
      linarith
    · have : eps0 / ((j : ℝ) + 2) < eps0 :=
        (div_lt_self heps0 (by linarith))
      linarith
  · have hd : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have h : Tendsto (fun j : ℕ => (1 : ℝ) + eps0 / ((j : ℝ) + 2))
        atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hd)
    simpa only [add_zero] using h

end M60

end PoincareConjecture
