import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaVariationalComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereAlphaEnergy_minimizing_sequence [T2Space M] [SecondCountableTopology M]
    (g : RiemannianMetric n M) (alpha : ℝ) (x : M)
    (hpi : Nontrivial (HomotopyGroup.Pi 2 M x)) :
    ∃ f : ℕ → UnitTwoSphere → M,
      (∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)) ∧
      (∀ j, ¬ IsNullHomotopicSphere (f j)) ∧
      Antitone (fun j => m60SphereAlphaEnergy g alpha (f j)) ∧
      Tendsto (fun j => m60SphereAlphaEnergy g alpha (f j)) atTop
        (𝓝 (sInf (m60NonNullAlphaEnergyValues g alpha))) := by
  obtain ⟨f0, hf0, hn0⟩ := m60_exists_smooth_nonNull_sphere_of_nontrivial_pi2 (n := n) x hpi
  have hne : (m60NonNullAlphaEnergyValues g alpha).Nonempty :=
    ⟨_, f0, hf0, hn0, rfl⟩
  obtain ⟨e, he, hlim, hmem⟩ := exists_seq_tendsto_sInf hne
    (m60NonNullAlphaEnergyValues_bddBelow g alpha)
  choose f hf hn henergy using hmem
  refine ⟨f, hf, hn, ?_, ?_⟩
  · simpa only [henergy] using he
  · simpa only [henergy] using hlim

end PoincareConjecture
