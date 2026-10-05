import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.MinimalSphere
import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.CurveShortening.Ramp.Geometry
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.LegacyTheory

/-!
# M60 filling areas and sphere-area estimates

All conclusions concern the displayed metric, sphere map, loop or flow.
Earlier theorem services are supplied only in the proof entry. Sources and
the complete derivation are in `reviews/contracts/M60-round1.md`; the printed
area-variation and annular corrections are in
`reviews/errata/2026-09-14-sphere-area.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

open MeasureTheory

universe u

namespace PoincareMT

/-- Finite actual functionals for a specified C1 sphere map, with the usual
area-energy comparison and equality in the weakly conformal case. -/
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

/-- Filling-area conclusions on the actual C1 loop space for a chosen metric.
Existence and near-minimizers concern null loops; reparameterization compares
the same admissible disk maps and their actual areas. -/
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

/-- A positive least area among all non-nullhomotopic C1 sphere maps, attained
by a smooth branched minimal sphere. No individual free class is prescribed. -/
def M60LeastSphereAreaConclusion
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Prop :=
  ∃ e₀ : ℝ, 0 < e₀ ∧
    (∀ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 f →
      m60SphereArea g f < e₀ → IsNullHomotopicSphere f) ∧
    ∃ f : UnitTwoSphere → M, M60BranchedMinimalSphere g f ∧
      ¬ IsNullHomotopicSphere f ∧ m60SphereArea g f = e₀

/-- Variation of a fixed sphere map along its actual flow on the same closed
slab, including rank-deficient maps and both time orders. -/
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

/-- The selected-time branched-minimal estimate in dimension three, with
attainment of the actual scalar minimum and its explicit specialization. -/
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

/-- The analytic and filling construction; its geometric inputs are primitive.
The short-loop consequence is assembled separately from the actual M58 output. -/
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

/-- The corrected M58 threshold and its same disk witness, with the checked
infimum consequence. Neither pi2 nor pi3 triviality is a hypothesis. -/
def M60ShortLoopAreaClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
  IsCompact (Set.univ : Set M) → ∀ η : ℝ, 0 < η →
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < η / 2 ∧
      ∀ γ : C1FreeLoopSpace (M := M), freeLoopLength g γ < ζ →
        ∃ D : LipschitzSpanningDisk g γ, D.area < η ∧
          fillingArea g γ ≤ D.area ∧ fillingArea g γ < η

/-- All seven source-node conclusions, with no predecessor theorem bundle in
the mathematical output. The unrestricted infimum-to-disk theorem is the
checked `m60FillingArea_le_disk` in the assigned helper file. -/
structure M60AreaTheory : Prop extends M60AreaCore.{u} where
  short_loop : M60ShortLoopAreaClaim.{u}

end PoincareMT
