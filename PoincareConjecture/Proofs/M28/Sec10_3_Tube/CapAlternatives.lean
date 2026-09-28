import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapRatio
import PoincareConjecture.Statements.M25NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}




def regionHasTubeOrFibration {X : Set M} (R : NeckCapRegion g X) : Prop :=
  match R with
  | .twoCaps _ _ _ _ _ _ => False
  | .singleCap _ _ => False
  | .doubleCappedTube _ _ _ _ => True
  | .cappedTube _ _ => True
  | .tube _ => True
  | .fibration _ => True




theorem regionHasTubeOrFibration_of_scalar_ratio
    (H : ConnectedNeckCapCover g) (D : LeviCivitaData g)
    (R : RepairedNeckCapTopologyData g H)
    {x y : M} (hx : x ∈ H.X) (hy : y ∈ H.X)
    (hlarge : H.cap_constant ^ 2 * D.scalarCurvature x < D.scalarCurvature y) :
    regionHasTubeOrFibration R.region := by
  obtain ⟨R, hcompat⟩ := R
  cases R with
  | twoCaps kind N N' component hunion hcontains =>
      change False
      obtain ⟨_, _, hC, hC'⟩ := hcompat
      have hconn : IsPreconnected (N.carrier ∪ N'.carrier) :=
        hunion ▸ component.connected.isPreconnected
      have hbound := N.scalar_le_sq_mul_on_union N' D hC hC'
        (N.inter_nonempty_of_preconnected_union N' hconn)
        (hunion ▸ hcontains hx) (hunion ▸ hcontains hy)
      exact (not_lt_of_ge hbound) hlarge
  | singleCap N hcontains =>
      change False
      obtain ⟨_, hC⟩ := hcompat
      have hxN := hcontains hx
      have hyN := hcontains hy
      have hbound := N.scalar_le_sq_mul_on_union N D hC hC ⟨x, hxN, hxN⟩
        (Or.inl hxN) (Or.inl hyN)
      exact (not_lt_of_ge hbound) hlarge
  | doubleCappedTube _ _ _ _ => trivial
  | cappedTube _ _ => trivial
  | tube _ => trivial
  | fibration _ => trivial





theorem exists_tube_or_fibration_region (P : RepairedNeckCapTopologyTheory.{u})
    (H : ConnectedNeckCapCover g) (hsmall : H.epsilon ≤ P.epsilon₀)
    (D : LeviCivitaData g) {x y : M} (hx : x ∈ H.X) (hy : y ∈ H.X)
    (hlarge : H.cap_constant ^ 2 * D.scalarCurvature x < D.scalarCurvature y) :
    ∃ R : RepairedNeckCapTopologyData g H, regionHasTubeOrFibration R.region := by
  obtain ⟨R⟩ := P.a21 g H hsmall
  exact ⟨R, regionHasTubeOrFibration_of_scalar_ratio H D R hx hy hlarge⟩

end PoincareConjecture.M28
