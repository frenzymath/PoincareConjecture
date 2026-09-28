import PoincareConjecture.Definitions.M60MinimalSpheres
import PoincareConjecture.Definitions.M53SphereSeparation
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Definitions.Ch19.RampEstimates
import PoincareConjecture.Statements.Ch18.LoopSpaceWidth

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

open MeasureTheory

universe u

namespace PoincareConjecture

structure M60SphereAreaProperties
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M) : Prop where
  area_integrable : Integrable (m60SphereAreaDensity g f) volume
  energy_integrable : Integrable (m60SphereEnergyDensity g f) volume
  area_nonnegative : 0 ≤ m60SphereArea g f
  area_le_energy : m60SphereArea g f ≤ m60SphereEnergy g f
  conformal_equality : M60WeaklyConformal g f →
    m60SphereArea g f = m60SphereEnergy g f

structure M60FillingAreaProperties
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) : Prop where
  filling_data : ∀ γ : C1FreeLoopSpace (M := M), IsNullHomotopicLoop γ →
    Nonempty (FillingAreaData g γ)
  nonnegative : ∀ γ : C1FreeLoopSpace (M := M), IsNullHomotopicLoop γ →
    0 ≤ fillingArea g γ
  near_minimizer : ∀ γ : C1FreeLoopSpace (M := M), IsNullHomotopicLoop γ →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ D : LipschitzSpanningDisk g γ, D.area < fillingArea g γ + epsilon
  reparameterization : ∀ γ₁ γ₂ : C1FreeLoopSpace (M := M),
    ReparameterizedLoops γ₁ γ₂ → fillingArea g γ₁ = fillingArea g γ₂
  continuous_on_null_loops : ContinuousOn
    (fun γ : C1FreeLoopSpace (M := M) => fillingArea g γ)
    {γ | IsNullHomotopicLoop γ}

def M60LeastSphereAreaConclusion
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Prop :=
  ∃ e₀ : ℝ, 0 < e₀ ∧
    (∀ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 f →
      m60SphereArea g f < e₀ → IsNullHomotopicSphere f) ∧
    ∃ f : UnitTwoSphere → M, M60BranchedMinimalSphere g f ∧
      ¬ IsNullHomotopicSphere f ∧ m60SphereArea g f = e₀

structure M60FixedMapAreaProperties
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (D : ℝ)
    (f : UnitTwoSphere → M) : Prop where
  continuous : ContinuousOn (fun t => m60SphereArea (F.metric t) f) (Set.Icc a b)
  ricci_trace_integrable : ∀ t ∈ Set.Icc a b,
    Integrable (m60SphereRicciTraceDensity (F.connection t) f) volume
  variation : ∀ t ∈ Set.Icc a b,
    HasDerivWithinAt (fun s => m60SphereArea (F.metric s) f)
      (-(∫ z : LoopPlane, m60SphereRicciTraceDensity (F.connection t) f z ∂volume))
      (Set.Icc a b) t
  absolute_derivative_bound : ∀ t ∈ Set.Icc a b,
    |-(∫ z : LoopPlane, m60SphereRicciTraceDensity (F.connection t) f z ∂volume)| ≤
      4 * D * m60SphereArea (F.metric t) f
  integrating_factor : AntitoneOn
    (fun t => Real.exp (-4 * D * (t - a)) * m60SphereArea (F.metric t) f)
    (Set.Icc a b)
  exponential_comparison : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
    m60SphereArea (F.metric t) f ≤
      Real.exp (4 * D * (t - s)) * m60SphereArea (F.metric s) f
  two_sided_comparison : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
    m60SphereArea (F.metric t) f ≤
      Real.exp (4 * D * |t - s|) * m60SphereArea (F.metric s) f

structure M60MinimalSphereVariationProperties
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b))
    (f : UnitTwoSphere → M) (t : ℝ) : Prop where
  scalar_minimum : IsLeast (Set.range (F.connection t).scalarCurvature)
    (m60ScalarMinimum (F.connection t))
  variation_bound : ∃ areaDerivative : ℝ,
    HasDerivWithinAt (fun s => m60SphereArea (F.metric s) f)
      areaDerivative (Set.Icc a b) t ∧
    (∀ ρ : ℝ, (∀ x : M, ρ ≤ (F.connection t).scalarCurvature x) →
      areaDerivative ≤ -4 * Real.pi - (ρ / 2) * m60SphereArea (F.metric t) f) ∧
    areaDerivative ≤ -4 * Real.pi -
      (m60ScalarMinimum (F.connection t) / 2) * m60SphereArea (F.metric t) f

structure M60AreaCore : Prop where
  sphere_functionals : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M]
      (g : RiemannianMetric n M) (f : UnitTwoSphere → M),
    ContMDiff (𝓡 2) (𝓡 n) 1 f → M60SphereAreaProperties g f
  filling : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
    IsCompact (Set.univ : Set M) → M60FillingAreaProperties g
  least_sphere : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric n M),
    IsCompact (Set.univ : Set M) → ∀ x : M,
      Nontrivial (HomotopyGroup.Pi 2 M x) → M60LeastSphereAreaConclusion g
  fixed_map : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M] {a b : ℝ}, a < b →
    ∀ (F : RicciFlow n M (Set.Icc a b)), IsCompact (Set.univ : Set M) →
    ∀ D : ℝ, 0 ≤ D →
      (∀ t ∈ Set.Icc a b, ∀ x : M, (F.connection t).ricciNormSq x ≤ D ^ 2) →
    ∀ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 f →
      M60FixedMapAreaProperties F D f
  minimal_variation : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] {a b : ℝ}, a < b →
    ∀ (F : RicciFlow 3 M (Set.Icc a b)), IsCompact (Set.univ : Set M) →
    ∀ (f : UnitTwoSphere → M) (t : ℝ), t ∈ Set.Icc a b →
      M60BranchedMinimalSphere (F.metric t) f →
        M60MinimalSphereVariationProperties F f t

def M60ShortLoopAreaClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
  IsCompact (Set.univ : Set M) → ∀ η : ℝ, 0 < η →
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < η / 2 ∧
      ∀ γ : C1FreeLoopSpace (M := M), freeLoopLength g γ < ζ →
        ∃ D : LipschitzSpanningDisk g γ, D.area < η ∧
          fillingArea g γ ≤ D.area ∧ fillingArea g γ < η

structure M60AreaTheory : Prop extends M60AreaCore.{u} where
  short_loop : M60ShortLoopAreaClaim.{u}

end PoincareConjecture
