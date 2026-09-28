import PoincareConjecture.Proofs.M15.Thm8_10_PathProjection
import PoincareConjecture.Proofs.M15.Thm8_10_PathLift
import PoincareConjecture.Statements.M14GeneralizedLGeometry










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {I : SpacetimeInterval}



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

end PoincareConjecture.Proofs.M15
