import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareLib.Geometry.Riemannian.ScalarOperators

/-!
# Necks and intrinsic curvature quantities

Adapted from Mapher, `PoincareMT/Definitions/Ch09/NeckCapTopology.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

noncomputable def scalarCurvatureSupOn (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (X : Set M) : ℝ :=
  sSup (Set.range (fun z : {x : M // x ∈ X} => D.scalarCurvature z.1))

noncomputable def scalarGradientNorm (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (x : M) : ℝ :=
  sSup (Set.range (fun v :
      {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} =>
    |mvfderiv (𝓡 3) D.scalarCurvature x v.1|))

noncomputable def intrinsicEDist (g : RiemannianMetric 3 M)
    (X : Set M) (x y : M) : ℝ≥0∞ :=
  sInf {L | ∃ γ : ℝ → M,
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc (0 : ℝ) 1) ∧
      γ 0 = x ∧ γ 1 = y ∧ γ '' Set.Icc (0 : ℝ) 1 ⊆ X ∧
        L = g.pathELength γ 0 1}

noncomputable def intrinsicDiameter (g : RiemannianMetric 3 M)
    (X : Set M) : ℝ≥0∞ :=
  sSup (Set.range (fun p : X × X => intrinsicEDist g X p.1 p.2))

abbrev NeckDomain (ε : ℝ) :=
  UnitTwoSphere × {s : ℝ // s ∈ Set.Ioo (-ε⁻¹) ε⁻¹}

structure NeckMetricJetComparison
    (g : RiemannianMetric 3 M) (ε scale : ℝ)
    (coordinate : UnitTwoSphere × ℝ → M) where
  close : RoundCylinderClose ε 0 (fun z v w ↦
    scale⁻¹ ^ 2 * roundCylinderPullback g coordinate z v w)

structure EpsilonNeck (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  scale : ℝ
  scale_pos : 0 < scale
  center : M
  connection : LeviCivitaData g
  scalar_center_pos : 0 < connection.scalarCurvature center
  scale_eq_scalar : scale = (connection.scalarCurvature center) ^ (-1 / 2 : ℝ)
  carrier : Set M
  carrier_open : IsOpen carrier
  coordinate : NeckDomain epsilon ≃ₜ carrier
  coordinate_map : UnitTwoSphere × ℝ → M
  coordinate_map_eq : ∀ z : NeckDomain epsilon,
    coordinate z = coordinate_map (z.1, (z.2 : ℝ))
  coordinate_map_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate_map
      (Set.univ ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
  coordinate_inverse : M → UnitTwoSphere × ℝ
  coordinate_inverse_mem : ∀ x ∈ carrier,
    coordinate_inverse x ∈ Set.univ ×ˢ Set.Ioo (-epsilon⁻¹) epsilon⁻¹
  coordinate_inverse_left : ∀ z : NeckDomain epsilon,
    coordinate_inverse (coordinate z) = (z.1, (z.2 : ℝ))
  coordinate_inverse_right : ∀ x hx,
    coordinate ((coordinate_inverse x).1,
      ⟨(coordinate_inverse x).2, (coordinate_inverse_mem x hx).2⟩) = ⟨x, hx⟩
  coordinate_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ coordinate_inverse carrier
  central_sphere : Set M
  central_sphere_eq : central_sphere =
    coordinate_map '' (Set.univ ×ˢ ({0} : Set ℝ))
  center_on_central_sphere : center ∈ central_sphere
  central_sphere_subset : central_sphere ⊆ carrier
  metric_comparison : NeckMetricJetComparison g epsilon scale coordinate_map

def EpsilonNeck.region {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (a b : ℝ) : Set M :=
  {x | x ∈ N.carrier ∧ a < (N.coordinate_inverse x).2 ∧
    (N.coordinate_inverse x).2 < b}

end PoincareMT
