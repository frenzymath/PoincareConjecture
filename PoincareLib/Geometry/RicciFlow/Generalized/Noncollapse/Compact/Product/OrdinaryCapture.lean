import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Product.PathProjection
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Product.PathLift
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Thm8_10_OrdinaryCapture.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Full ordinary capture in the actual product spacetime

Morgan-Tian Remark 3.37, p. 60, and Theorem 8.10, p. 177.
The actual projection and lift supply all input fields of M14 capture;
the product cylinder covers the whole spacetime.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-ordinary-capture.md`.
-/

set_option autoImplicit false
-- The product representatives use the same selected interval instances.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {I : SpacetimeInterval}

/-- The actual ordinary product satisfies M14's full capture input.
Source: Remark 3.37, p. 60, used in Theorem 8.10, p. 177. -/
theorem ordinaryProduct_capture
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    (T taumax : ℝ) (hT : T ∈ I.domain) :
    Nonempty (M14OrdinaryCaptureData (ordinaryProductTransport F P) M I
      P.product.productCylinder (ordinaryProductCylinderMetric F P) F T taumax) := by
  classical
  let G := ordinaryProductTransport F P
  let Q (a b : ℝ) (x y : G.Point) (p : M14BackwardPath G T a b x y) :=
    (ordinaryProduct_backwardPath_projection hM12 F P hT p).choose
  have hQ (a b : ℝ) (x y : G.Point) (p : M14BackwardPath G T a b x y) :
      (Q a b x y p).curve = fun s => (p.curve s).2 :=
    (ordinaryProduct_backwardPath_projection hM12 F P hT p).choose_spec
  refine ⟨{
    metric_eq := fun _ _ => rfl
    point_map := fun q => q.2
    point_map_on_cylinder := ?_
    point_map_continuous := (ordinaryProduct_spatial_smooth F P).continuous.continuousOn
    path_map := fun a b x y p _ => Q a b x y p
    path_start_eq := ?_
    path_end_eq := ?_
    path_curve_eq := ?_
    path_capture_eq := ?_
    path_lift := fun _ _ q => ordinaryProduct_backwardPath_lift hM12 F P q
    capture_from_start := ?_
  }⟩
  · intro t x
    exact congrArg Prod.snd (P.product.productCylinder_eq (t, x))
  · intro a b x y p _
    rw [hQ]
    exact congrArg Prod.snd p.curve_start
  · intro a b x y p _
    rw [hQ]
    exact congrArg Prod.snd p.curve_end
  · intro a b x y p _ s _
    rw [hQ]
  · intro a b x y p _ s hs
    rw [P.product.productCylinder_eq, hQ]
    apply Prod.ext
    · exact Subtype.ext (p.curve_time s hs).symm
    · rfl
  · intro _ _ _ _ _ _ p s _
    rw [ordinaryProductCylinder_range F P]
    exact mem_univ (p.curve s)

end PoincareMT.Generalized.Noncollapse
