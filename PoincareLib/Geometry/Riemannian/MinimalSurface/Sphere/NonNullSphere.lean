import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Homotopy.NonNull.Sphere
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Homotopy.NonNull.Smoothing

/-!
# Nonemptiness of the smooth non-null sphere class

Morgan-Tian Lemma 18.10, printed pp. 424-425, starts with nontrivial
second homotopy. A genuine sphere representative is smoothed through an
actual homotopy, producing a competitor for the least-energy construction.
The conclusion uses the frozen sphere and null-homotopy definitions.
-/

set_option autoImplicit false

open scoped Topology Manifold ContDiff

universe u

namespace PoincareMT

/-- Nontrivial second homotopy supplies an actual smooth non-null sphere.
This is the nonemptiness step of MT Lemma 18.10, printed pp. 424-425.
The construction does not need target compactness or a chosen metric. -/
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

end PoincareMT
