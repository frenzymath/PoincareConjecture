import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinCoveredBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

structure M64IntrinsicJoinedBandPatch (gamma : Bool → ℝ → AnnulusCoordinates)
    (T b : Bool → ℝ) (U : Set AnnulusCoordinates) where
  frame : Bool → (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates
  graph : Bool → ℝ → ℝ
  left : Bool → ℝ
  right : Bool → ℝ
  increasing : ∀ e, left e < right e
  direction : AnnulusCoordinates
  left_length : ℝ
  middle_length : ℝ
  right_length : ℝ
  band : ∀ e : Bool, ObliqueBandFaces
    (collarParameterEquiv.trans (frame e)).toHomeomorph.toOpenPartialHomeomorph
    (graph e) (left e) (right e)
    ((frame e).symm direction).1 ((frame e).symm direction).2
    ((frame e).symm direction).1 ((frame e).symm direction).2
    (if e then middle_length else left_length) (if e then right_length else middle_length)
  left_base : ∀ e : Bool, frame e (left e, graph e (left e)) =
    if e then gamma false (T false) else gamma false (b false)
  right_base : ∀ e : Bool, frame e (right e, graph e (right e)) =
    if e then gamma true (b true) else gamma false (T false)
  transverse : ∀ e, 0 < inner ℝ (quarterTurn (deriv (gamma e) (b e))) direction
  tangent : ∀ e : Bool, ∃ v : ℝ, 0 < v ∧ deriv (gamma e) (b e) =
    v • frame e (1, deriv (graph e) (if e then right e else left e))
  lower_arc : ∀ e : Bool, (band e).lowerArc =
    if e then gamma e '' Icc 0 (b e) else gamma e '' Icc (b e) (T e)
  occupied : ∀ e, (band e).carrier ⊆ closure U
  off_lower : ∀ e, (band e).carrier \ (band e).lowerArc ⊆ U
  intersection : (band false).carrier ∩ (band true).carrier =
    segment ℝ (gamma false (T false)) (gamma false (T false) + middle_length • direction)

namespace M64IntrinsicJoinedBandPatch

variable {gamma : Bool → ℝ → AnnulusCoordinates} {T b : Bool → ℝ}
  {U : Set AnnulusCoordinates} (P : M64IntrinsicJoinedBandPatch gamma T b U)

theorem outer_length_pos (e : Bool) : 0 < (if e then P.right_length else P.left_length) := by
  cases e
  · exact (P.band false).left_length_pos
  · exact (P.band true).right_length_pos

theorem middle_length_pos : 0 < P.middle_length := (P.band false).right_length_pos

theorem outer_base (e : Bool) :
    P.frame e (if e then P.right e else P.left e,
      P.graph e (if e then P.right e else P.left e)) = gamma e (b e) := by
  cases e
  · exact P.left_base false
  · exact P.right_base true

theorem outer_cut (e : Bool) : (if e then (P.band e).rightCut else (P.band e).leftCut) =
    segment ℝ (gamma e (b e))
      (gamma e (b e) + (if e then P.right_length else P.left_length) • P.direction) := by
  cases e
  · change (P.band false).leftCut = _
    rw [m64Intrinsic_band_left_cut (P.frame false) (P.band false), P.left_base]
    simp only [Bool.false_eq_true, if_false, Prod.eta, ContinuousLinearEquiv.apply_symm_apply]
  · change (P.band true).rightCut = _
    rw [m64Intrinsic_band_right_cut (P.frame true) (P.band true), P.right_base]
    simp only [if_true, Prod.eta, ContinuousLinearEquiv.apply_symm_apply]

theorem inner_cut (e : Bool) : (if e then (P.band e).leftCut else (P.band e).rightCut) =
    segment ℝ (gamma false (T false))
      (gamma false (T false) + P.middle_length • P.direction) := by
  cases e
  · change (P.band false).rightCut = _
    rw [m64Intrinsic_band_right_cut (P.frame false) (P.band false), P.right_base]
    simp only [Bool.false_eq_true, if_false, Prod.eta, ContinuousLinearEquiv.apply_symm_apply]
  · change (P.band true).leftCut = _
    rw [m64Intrinsic_band_left_cut (P.frame true) (P.band true), P.left_base]
    simp only [if_true, Prod.eta, ContinuousLinearEquiv.apply_symm_apply]

theorem outer_endpoint_zero (e : Bool) :
    ((P.band e).endpointEdge e).map 0 = gamma e (b e) := by
  cases e
  · rw [m64Intrinsic_band_left_endpoint_zero]
    exact P.left_base false
  · rw [m64Intrinsic_band_right_endpoint_zero]
    exact P.right_base true

end M64IntrinsicJoinedBandPatch

end PoincareConjecture
