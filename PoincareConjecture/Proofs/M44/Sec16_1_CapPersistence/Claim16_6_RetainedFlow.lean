import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoordinateFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedRicciEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T b : ℝ}

theorem retainedChartCoefficients_symm
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) (t : ℝ) (x v w : E) :
    retainedChartCoefficients event G q (t, x) v w =
      retainedChartCoefficients event G q (t, x) w v := by
  unfold retainedChartCoefficients
  split_ifs
  · exact (event.pre_flow.metric t).symm _ _ _
  · exact (G.metric t).symm _ _ _

theorem retainedChartCoefficients_pos
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b))
    (q : (slice event.tMinus).carrier) {U : Set E}
    (hchart : U ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre)
    (t : ℝ) {x : E} (hx : x ∈ U) (v : E) (hv : v ≠ 0) :
    0 < retainedChartCoefficients event G q (t, x) v v := by
  unfold retainedChartCoefficients
  split_ifs
  · have hi : (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm x).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hchart hx)
    apply (event.pre_flow.metric t).pos
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    exact hz
  · have hi := retained_inverse_coordinates_invertible event q hchart hret hx
    apply (G.metric t).pos
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    exact hz

set_option maxHeartbeats 800000 in

theorem exists_retained_coordinate_flow
    (event : SurgeryEventData g0 K P slice metric T)
    (G : RicciFlow 3 (slice T).carrier (Icc T b)) (hTb : T < b)
    (hbirth : G.metric T = metric T)
    (q : (slice event.tMinus).carrier) (hq : q ∈ interior event.retained_pre)
    (U : Opens E) (hchart : (U : Set E) ⊆ (extChartAt (𝓡 3) q).target)
    (hret : (extChartAt (𝓡 3) q).symm '' U ⊆ interior event.retained_pre) :
    ∃ F : RicciFlow 3 U (Ioo event.tMinus b),
      ∀ t, ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        (F.metric t).inner x v w = retainedChartCoefficients event G q (t, x) v w := by
  obtain ⟨hsmooth, hevol⟩ := retainedChartCoefficients_smooth_ricci
    event G hTb hbirth q hq U.isOpen hchart hret
  apply exists_ricciFlow_of_open_coefficients U ordConnected_Ioo
    (Ioo_infinite (event.tMinus_lt.trans hTb)).nontrivial
    (retainedChartCoefficients event G q)
    (retainedChartCoefficients_spatial_smooth event G q U.isOpen hchart hret)
    (fun t x _ v w => retainedChartCoefficients_symm event G q t x v w)
    (fun t _ hx v hv => retainedChartCoefficients_pos event G q hchart hret t hx v hv)
    hsmooth
  intro t ht x hx
  exact HasFDerivAt.hasFDerivWithinAt (hevol t ht x hx)

end PoincareConjecture.M44
