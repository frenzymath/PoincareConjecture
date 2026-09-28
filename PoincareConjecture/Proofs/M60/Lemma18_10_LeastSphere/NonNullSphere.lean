import PoincareConjecture.Definitions.M53SphereSeparation
import PoincareConjecture.Proofs.M60.Mathlib.NonNullSphere
import PoincareConjecture.Proofs.M60.Mathlib.NonNullSmoothing










set_option autoImplicit false

open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture




theorem m60_exists_smooth_nonNull_sphere_of_nontrivial_pi2
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (x : M) (hpi : Nontrivial (HomotopyGroup.Pi 2 M x)) :
    ∃ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) ∞ f ∧
      ¬ IsNullHomotopicSphere f := by
  let := hpi
  obtain ⟨f, hf⟩ := M60.exists_nonNull_sphere_of_nontrivial_homotopyGroup 1 x
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 n) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨g, hg, hhom⟩ := M60.exists_smooth_homotopic_of_compact
    (E := EuclideanSpace ℝ (Fin 2)) (F := EuclideanSpace ℝ (Fin n)) f
  refine ⟨g, hg, ?_⟩
  rintro ⟨_, y, hnull⟩
  apply hf
  exact ⟨y, hhom.symm.trans hnull⟩

end PoincareConjecture
