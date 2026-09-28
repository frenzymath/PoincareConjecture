import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.TrimmedBoundaryApproximation
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StabilizedBoundaryGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.C1LabelGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StripBoundaryImmersion














set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}
  {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {r epsilon : ℝ}





theorem exists_stabilized_trimmed_boundary_tolerance
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon)
    (htime : time ∈ Icc a b) (hr : 0 < r)
    (hC2 : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 2 S.separated.minimum.map
      {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 4 ∧
      ∀ width : ℝ, 0 < width → width < delta →
        TrimmedBoundaryControl Q.flow time S.separated.minimum.map r eta width ∧
        |m62Length Q.flow (fun y _ => S.separated.minimum.map (annulusPoint y width)) time -
          m62Length P.flow (fun y _ => gamma0 y) time| < eta + epsilon / 2 ∧
        |m62Length Q.flow (fun y _ => S.separated.minimum.map (annulusPoint y (1 - width))) time -
          m62Length P.flow (fun y _ => gamma1 y) time| < eta + epsilon / 2 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let B := S.separated.minimum
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ S.approximation.first
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset) ∘ S.approximation.second
  have hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 2 c0 :=
    S.lower_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 2 c1 :=
    S.upper_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hp0 : Function.Periodic c0 curvePeriod :=
    S.approximation.first_periodic.comp (auxiliaryCircleSection Q (Q.circle.quotient 0))
  have hp1 : Function.Periodic c1 curvePeriod :=
    S.approximation.second_periodic.comp
      (auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset))
  have hb0 : (fun y => B.map (annulusPoint y 0)) =
      c0 ∘ S.separated.first_label.map := funext B.lower_boundary
  have hb1 : (fun y => B.map (annulusPoint y 1)) =
      c1 ∘ S.separated.second_label.map := funext B.upper_boundary
  have himm0 := annulus_closedStrip_slice_immersed B S.separated.closed_c1
    (fun p hp => (S.separated.within_immersion p hp).2.2)
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have himm1 := annulus_closedStrip_slice_immersed B S.separated.closed_c1
    (fun p hp => (S.separated.within_immersion p hp).2.2)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hlabelImm0 : ∀ x, curveVelocity (n := (n + 1) + 1)
      (c0 ∘ S.separated.first_label.map) x ≠ 0 := by
    rwa [hb0] at himm0
  have hlabelImm1 : ∀ x, curveVelocity (n := (n + 1) + 1)
      (c1 ∘ S.separated.second_label.map) x ≠ 0 := by
    rwa [hb1] at himm1
  have hgeom0 := c1_lift_subarc_geometry Q.flow htime hc0 hp0 S.lower_immersed
    S.separated.first_label S.separated.first_label_c1 hlabelImm0
  have hgeom1 := c1_lift_subarc_geometry Q.flow htime hc1 hp1 S.upper_immersed
    S.separated.second_label S.separated.second_label_c1 hlabelImm1
  have hlen0 : m62Length Q.flow (fun y _ => B.map (annulusPoint y 0)) time =
      m62Length Q.flow (fun y _ => c0 y) time := by
    simpa only [B.lower_boundary, c0, Function.comp_apply] using hgeom0.1
  have hlen1 : m62Length Q.flow (fun y _ => B.map (annulusPoint y 1)) time =
      m62Length Q.flow (fun y _ => c1 y) time := by
    simpa only [B.upper_boundary, c1, Function.comp_apply] using hgeom1.1
  have hlong : r / 2 < m62Length Q.flow (fun y _ => B.map (annulusPoint y 0)) time := by
    rw [hlen0]
    exact S.lower_length_strict
  have hlabelTurn := c1_lift_turning_bound Q.flow htime hc0 hp0 S.lower_immersed
    S.separated.first_label S.separated.first_label_c1 hlabelImm0 S.lower_turning
  have hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength Q.flow (fun y _ => B.map (annulusPoint y 0)) time alpha beta ≤ r / 2 →
      m63ArcTotalCurvature Q.flow (fun y _ => B.map (annulusPoint y 0)) time alpha beta <
        (3 / 400 : ℝ) := by
    simpa only [B.lower_boundary, c0, Function.comp_apply] using hlabelTurn
  obtain ⟨delta, hdelta, hquarter, htrim⟩ := exists_trimmed_boundary_tolerance Q.flow htime
    hC2 S.separated.interior_smooth (fun s _ x => B.periodic x s) himm0 himm1 hr hlong hturn heta
  refine ⟨delta, hdelta, hquarter, ?_⟩
  intro width hwidth hsmall
  have T := htrim width hwidth hsmall
  refine ⟨T, ?_, ?_⟩
  · have hnear : |m62Length Q.flow (fun y _ => B.map (annulusPoint y width)) time -
        m62Length Q.flow (fun y _ => c0 y) time| < eta := by
      have h := T.lower_length_error
      change |m62Length Q.flow (fun y _ => B.map (annulusPoint y width)) time -
        m62Length Q.flow (fun y _ => B.map (annulusPoint y 0)) time| < eta at h
      exact hlen0 ▸ h
    exact (abs_sub_le _ (m62Length Q.flow (fun y _ => c0 y) time) _).trans_lt
      (add_lt_add hnear S.lower_length_error)
  · have hnear : |m62Length Q.flow (fun y _ => B.map (annulusPoint y (1 - width))) time -
        m62Length Q.flow (fun y _ => c1 y) time| < eta := by
      have h := T.upper_length_error
      change |m62Length Q.flow (fun y _ => B.map (annulusPoint y (1 - width))) time -
        m62Length Q.flow (fun y _ => B.map (annulusPoint y 1)) time| < eta at h
      exact hlen1 ▸ h
    exact (abs_sub_le _ (m62Length Q.flow (fun y _ => c1 y) time) _).trans_lt
      (add_lt_add hnear S.upper_length_error)

end PoincareConjecture.M64.RampTransport
