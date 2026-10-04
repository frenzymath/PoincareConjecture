import PoincareLib.Geometry.RicciFlow.Soliton.Basic
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder

/-!
# Shrinking sphere-line models and their free quotients

Ported from Mapher `Definitions/Ch09/ShrinkingSoliton.lean` at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`, with declarations unchanged.
Morgan--Tian, Theorem 9.42, pp. 206-208.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

section ThreeDimensional

variable {M₃ : Type u} [TopologicalSpace M₃]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₃]
  [IsManifold (𝓡 3) ∞ M₃] [MeasurableSpace M₃] [BorelSpace M₃]
  [T2Space M₃] [T3Space M₃] [SecondCountableTopology M₃]
  [ConnectedSpace M₃]

/-- A smooth nowhere-vanishing 3-form fixes the orientation convention. -/
structure SmoothOrientation3 {P : Type u}
    [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P]
    [IsManifold (𝓡 3) ∞ P] where
  form : ∀ p : P,
    AlternatingMap ℝ (TangentSpace (𝓡 3) p) ℝ (Fin 3)
  nonvanishing : ∀ p : P, ∃ u : Fin 3 → TangentSpace (𝓡 3) p,
    form p u ≠ 0
  smooth_on : ∀ (X : Fin 3 → (∀ p : P, TangentSpace (𝓡 3) p)),
    (∀ i, ContMDiff (𝓡 3)
      ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
      (fun p : P => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin 3)) (E := fun x : P => TangentSpace (𝓡 3) x)
        p (X i p))) →
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun p => form p (fun i => X i p))

/-- The literal shrinking round `S^2 x R` in a fixed smooth product gauge.
At time `-1` the sphere has Gaussian curvature `1/2` (MT p. 206). -/
structure SphereLineProductData {P : Type u}
    [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P]
    [IsManifold (𝓡 3) ∞ P] where
  surface : Type u
  surface_topology : TopologicalSpace surface
  surface_charted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface
  surface_manifold : IsManifold (𝓡 2) ∞ surface
  surface_sphere :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface := surface_charted
    letI : IsManifold (𝓡 2) ∞ surface := surface_manifold
    Diffeomorph (𝓡 2) (𝓡 2) surface UnitTwoSphere ∞
  surface_metric : ℝ → @RiemannianMetric 2 surface surface_topology
    surface_charted surface_manifold
  surface_connection : ∀ t, @LeviCivitaData 2 surface surface_topology
    surface_charted surface_manifold (surface_metric t)
  surface_round : ∀ t : ℝ, t < 0 →
    @ConstantPositiveSectionalCurvature 2 surface surface_topology
      surface_charted surface_manifold (surface_metric t) (surface_connection t)
  surface_inner_round : ∀ t : ℝ, t < 0 →
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface := surface_charted
    letI : IsManifold (𝓡 2) ∞ surface := surface_manifold
    ∀ p : surface, ∀ u v : TangentSpace (𝓡 2) p,
      (surface_metric t).inner p u v = (-2 * t) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : surface => (surface_sphere x).1) p u)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : surface => (surface_sphere x).1) p v)
  product_charted :
    letI : TopologicalSpace surface := surface_topology
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ)
  product_manifold :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    IsManifold (𝓡 3) ∞ (surface × ℝ)
  product_smooth_to_canonical :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface := surface_charted
    letI : IsManifold (𝓡 2) ∞ surface := surface_manifold
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (id : surface × ℝ → surface × ℝ)
  product_smooth_from_canonical :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface := surface_charted
    letI : IsManifold (𝓡 2) ∞ surface := surface_manifold
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (id : surface × ℝ → surface × ℝ)
  product_metric : ∀ _t : ℝ,
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    RiemannianMetric 3 (surface × ℝ)
  product_connection : ∀ t : ℝ,
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    LeviCivitaData (product_metric t)
  orientation :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    SmoothOrientation3 (P := surface × ℝ)
  product_equiv :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    Diffeomorph (𝓡 3) (𝓡 3) P (surface × ℝ) ∞
  tangent_surface_component : ∀ p : surface × ℝ,
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    TangentSpace (𝓡 3) p → TangentSpace (𝓡 2) p.1
  tangent_line_component : ∀ p : surface × ℝ,
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    TangentSpace (𝓡 3) p → ℝ
  tangent_surface_component_eq :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) surface := surface_charted
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    ∀ p : surface × ℝ, ∀ v : TangentSpace (𝓡 3) p,
      tangent_surface_component p v =
        mfderiv (𝓡 3) (𝓡 2) (Prod.fst : surface × ℝ → surface) p v
  tangent_line_component_eq :
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    ∀ p : surface × ℝ, ∀ v : TangentSpace (𝓡 3) p,
      tangent_line_component p v =
        mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (Prod.snd : surface × ℝ → ℝ) p v
  tangent_components_surjective : ∀ p : surface × ℝ,
    Function.Surjective (fun z ↦
      (tangent_surface_component p z, tangent_line_component p z))
  product_inner_formula : ∀ t : ℝ, t < 0 →
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    ∀ p : surface × ℝ, ∀ u v : TangentSpace (𝓡 3) p,
      (product_metric t).inner p u v =
          (surface_metric t).inner p.1 (tangent_surface_component p u)
          (tangent_surface_component p v) +
        tangent_line_component p u * tangent_line_component p v
/-- One fixed diffeomorphism identifies the entire negative-time flow with
the normalized round sphere-line product. -/
structure SphereLineProductCertificate {S : GradientShrinkingSolitonData 3 M₃}
    (G : ShrinkingSolitonFlow S) extends SphereLineProductData (P := M₃) where
  flow_isometric_to_product : ∀ t : ℝ, t < 0 →
    letI : TopologicalSpace surface := surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (surface × ℝ) := product_charted
    letI : IsManifold (𝓡 3) ∞ (surface × ℝ) := product_manifold
    ∀ p : M₃, ∀ u v : TangentSpace (𝓡 3) p,
      (G.flow.metric t).inner p u v =
        (product_metric t).inner (product_equiv p)
          (mfderiv (𝓡 3) (𝓡 3) product_equiv p u)
          (mfderiv (𝓡 3) (𝓡 3) product_equiv p v)

/-- The Theorem 9.42 quotient alternative, with a free isometric involution.
No orientation condition is imposed: this includes the `RP^2 x R` quotient. -/
structure QuotientSphereLineCertificate {S : GradientShrinkingSolitonData 3 M₃}
    (G : ShrinkingSolitonFlow S) where
  cover : Type u
  cover_topology : TopologicalSpace cover
  cover_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover
  cover_manifold : IsManifold (𝓡 3) ∞ cover
  product :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    SphereLineProductData (P := cover)
  involution :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    product.surface × ℝ → product.surface × ℝ
  involution_involutive :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    Function.Involutive involution
  involution_free :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    ∀ p, involution p ≠ p
  involution_smooth :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (product.surface × ℝ) :=
      product.product_charted
    letI : IsManifold (𝓡 3) ∞ (product.surface × ℝ) := product.product_manifold
    ContMDiff (𝓡 3) (𝓡 3) ∞ involution
  involution_isometry :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (product.surface × ℝ) :=
      product.product_charted
    letI : IsManifold (𝓡 3) ∞ (product.surface × ℝ) := product.product_manifold
    ∀ t : ℝ, t < 0 → ∀ p : product.surface × ℝ,
      ∀ u v : TangentSpace (𝓡 3) p,
        (product.product_metric t).inner p u v =
          (product.product_metric t).inner (involution p)
            (mfderiv (𝓡 3) (𝓡 3) involution p u)
            (mfderiv (𝓡 3) (𝓡 3) involution p v)
  quotient_carrier : Type u
  quotient_topology : TopologicalSpace quotient_carrier
  quotient_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) quotient_carrier
  quotient_manifold : IsManifold (𝓡 3) ∞ quotient_carrier
  quotient_map :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (product.surface × ℝ) :=
      product.product_charted
    letI : IsManifold (𝓡 3) ∞ (product.surface × ℝ) := product.product_manifold
    product.surface × ℝ → quotient_carrier
  quotient_map_smooth :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (product.surface × ℝ) :=
      product.product_charted
    letI : IsManifold (𝓡 3) ∞ (product.surface × ℝ) := product.product_manifold
    letI : TopologicalSpace quotient_carrier := quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) quotient_carrier := quotient_charted
    letI : IsManifold (𝓡 3) ∞ quotient_carrier := quotient_manifold
    ContMDiff (𝓡 3) (𝓡 3) ∞ quotient_map
  quotient_map_surjective :
    letI : TopologicalSpace cover := cover_topology
    letI : TopologicalSpace product.surface := product.surface_topology
    Function.Surjective quotient_map
  quotient_fiber_eq_orbit :
    letI : TopologicalSpace cover := cover_topology
    letI : TopologicalSpace product.surface := product.surface_topology
    ∀ p q, quotient_map p = quotient_map q ↔ q = p ∨ q = involution p
  quotient_flow :
    @RicciFlow 3 quotient_carrier quotient_topology quotient_charted quotient_manifold
      (Set.Iio 0)
  quotient_metric : ∀ _t : ℝ,
    @RiemannianMetric 3 quotient_carrier quotient_topology quotient_charted quotient_manifold
  quotient_connection : ∀ t : ℝ,
    @LeviCivitaData 3 quotient_carrier quotient_topology quotient_charted quotient_manifold
      (quotient_metric t)
  quotient_flow_metric : ∀ t : ℝ, t < 0 →
    quotient_flow.metric t = quotient_metric t
  /-- Chosen-data coherence, not an assertion that arbitrary connection
  records coincide on nonsmooth sections. -/
  quotient_flow_connection : ∀ t : ℝ, t < 0 →
    HEq (quotient_flow.connection t) (quotient_connection t)
  quotient_metric_pullback :
    letI : TopologicalSpace cover := cover_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) cover := cover_charted
    letI : IsManifold (𝓡 3) ∞ cover := cover_manifold
    letI : TopologicalSpace product.surface := product.surface_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (product.surface × ℝ) :=
      product.product_charted
    letI : IsManifold (𝓡 3) ∞ (product.surface × ℝ) := product.product_manifold
    letI : TopologicalSpace quotient_carrier := quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) quotient_carrier := quotient_charted
    letI : IsManifold (𝓡 3) ∞ quotient_carrier := quotient_manifold
    ∀ t : ℝ, t < 0 → ∀ p : product.surface × ℝ,
      ∀ u v : TangentSpace (𝓡 3) p,
        (product.product_metric t).inner p u v =
          (quotient_metric t).inner (quotient_map p)
            (mfderiv (𝓡 3) (𝓡 3) quotient_map p u)
            (mfderiv (𝓡 3) (𝓡 3) quotient_map p v)
  flow_isometric_to_quotient :
    letI : TopologicalSpace quotient_carrier := quotient_topology
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) quotient_carrier := quotient_charted
    letI : IsManifold (𝓡 3) ∞ quotient_carrier := quotient_manifold
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) M₃ quotient_carrier ∞, ∀ t : ℝ, t < 0 →
      ∀ p : M₃, ∀ u v : TangentSpace (𝓡 3) p,
        (G.flow.metric t).inner p u v =
          (quotient_metric t).inner (e p)
            (mfderiv (𝓡 3) (𝓡 3) e p u)
            (mfderiv (𝓡 3) (𝓡 3) e p v)

end ThreeDimensional

end PoincareMT
