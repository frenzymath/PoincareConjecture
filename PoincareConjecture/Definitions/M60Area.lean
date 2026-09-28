import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
















set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

open MeasureTheory

universe u

namespace PoincareConjecture


noncomputable def m60SpherePole : UnitTwoSphere :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0⟩


noncomputable def m60SphereChart :
    OpenPartialHomeomorph UnitTwoSphere LoopPlane :=
  letI : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
  stereographic' 2 m60SpherePole


noncomputable def m60SphereParameter : LoopPlane → UnitTwoSphere :=
  m60SphereChart.symm

section Carrier

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


noncomputable def m60AreaGram (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
  let d := mfderiv (𝓡 2) (𝓡 n) f z
  let e : Fin 2 → TangentSpace (𝓡 n) (f z) :=
    fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  fun i j => g.inner (f z) (e i) (e j)


noncomputable def m60AreaDensity (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  Real.sqrt (max 0 (Matrix.det (m60AreaGram g f z)))


noncomputable def m60EnergyDensity (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (m60AreaGram g f z)


noncomputable def m60SphereAreaDensity (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (z : LoopPlane) : ℝ :=
  m60AreaDensity g (f ∘ m60SphereParameter) z


noncomputable def m60SphereEnergyDensity (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (z : LoopPlane) : ℝ :=
  m60EnergyDensity g (f ∘ m60SphereParameter) z


noncomputable def m60SphereArea (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : ℝ :=
  ∫ z : LoopPlane, m60SphereAreaDensity g f z ∂volume


noncomputable def m60SphereEnergy (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : ℝ :=
  ∫ z : LoopPlane, m60SphereEnergyDensity g f z ∂volume



noncomputable def m60SphereRicciTraceDensity {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : UnitTwoSphere → M) (z : LoopPlane) : ℝ :=
  let F := f ∘ m60SphereParameter
  let d := mfderiv (𝓡 2) (𝓡 n) F z
  let e : Fin 2 → TangentSpace (𝓡 n) (F z) :=
    fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G := m60AreaGram g F z
  if Matrix.det G = 0 then 0
  else (∑ i : Fin 2, ∑ j : Fin 2, (G⁻¹) i j * D.ricci (F z) (e j) (e i)) *
    m60AreaDensity g F z



noncomputable def m60ScalarMinimum {g : RiemannianMetric n M}
    (D : LeviCivitaData g) : ℝ :=
  sInf (Set.range D.scalarCurvature)

end Carrier



theorem m60AreaDensity_eq_parametrizedAreaDensity
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity g f z = parametrizedAreaDensity g f z := rfl

end PoincareConjecture
