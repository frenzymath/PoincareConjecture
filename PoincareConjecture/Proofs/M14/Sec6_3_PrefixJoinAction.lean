import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinPath









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}




theorem action_prefixJoinPath_eq_blend (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) (D : PrefixJoinGauge q p)
    (d : ℝ) (hd : 0 < d) (hsmall : 2 * d < D.radius) :
    M14BackwardLAction G (prefixJoinPath hM12 q p D d hd hsmall) =
      (∫ t in τ₁..(c - 2 * d), M14BackwardLIntegrand G p t) +
        (∫ t in (c - 2 * d)..(c - d),
          M14RawLIntegrand G
            (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))
            (projectedCurveVelocity G
              (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))) t) +
        ∫ t in (c - d)..τ₂, M14BackwardLIntegrand G q t := by
  let γ := oneSidedGaugeJoin D.index D.lift p.curve q.curve c D.radius d
  let F := M14RawLIntegrand G γ (projectedCurveVelocity G γ)
  have ha : τ₁ < c - 2 * d := by linarith [D.left_margin]
  have hab : c - 2 * d < c - d := by linarith
  have hb : c - d < τ₂ := by linarith [D.right_margin, D.radius_pos]
  have hpRec (s : ℝ) (hs : s ∈ Icc (c - D.radius) c) :
      (G.gaugeCover.cylinder D.index).toSpacetime (D.lift (p.curve s)) = p.curve s :=
    D.lift_right _ (D.prefix_in_image s hs)
  have hqRec (s : ℝ) (hs : s ∈ Icc (c - D.radius) c) :
      (G.gaugeCover.cylinder D.index).toSpacetime (D.lift (q.curve s)) = q.curve s :=
    D.lift_right _ (D.continuation_in_image s ⟨hs.1, by linarith [hs.2, D.radius_pos]⟩)
  have hwhole : IntervalIntegrable F volume τ₁ τ₂ :=
    (prefixJoinPath hM12 q p D d hd hsmall).action_integrable
  have hleft : IntervalIntegrable F volume τ₁ (c - 2 * d) := hwhole.mono_set (by
    rw [uIcc_of_le ha.le, uIcc_of_le q.tau_lt.le]
    exact Icc_subset_Icc_right (hab.le.trans hb.le))
  have hmiddle : IntervalIntegrable F volume (c - 2 * d) (c - d) := hwhole.mono_set (by
    rw [uIcc_of_le hab.le, uIcc_of_le q.tau_lt.le]
    exact Icc_subset_Icc ha.le hb.le)
  have hright : IntervalIntegrable F volume (c - d) τ₂ := hwhole.mono_set (by
    rw [uIcc_of_le hb.le, uIcc_of_le q.tau_lt.le]
    exact Icc_subset_Icc_left (ha.le.trans hab.le))
  have hleftEq : (∫ s in τ₁..(c - 2 * d), F s) =
      ∫ s in τ₁..(c - 2 * d), M14BackwardLIntegrand G p s := by
    apply intervalIntegral.integral_congr_Ioo_of_le ha.le
    intro s hs
    apply rawLIntegrand_eq_backward_of_eventuallyEq p ⟨hs.1, by linarith [hs.2]⟩
    filter_upwards [gt_mem_nhds hs.2] with t ht
    exact oneSidedGaugeJoin_eq_left D.index D.lift p.curve q.curve hd hpRec
      (fun _ ht => D.overlap_time ht) ht.le
  have hmiddleEq : (∫ s in (c - 2 * d)..(c - d), F s) =
      ∫ s in (c - 2 * d)..(c - d),
        M14RawLIntegrand G
          (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))
          (projectedCurveVelocity G
            (gaugeBlend D.index D.lift p.curve q.curve (c - 3 * d / 2) (d / 2))) s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    apply rawLIntegrand_projectedVelocity_congr
    have hsI : s ∈ Ioo (c - D.radius) c := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    filter_upwards [isOpen_Ioo.mem_nhds hsI] with t ht
    exact oneSidedGaugeJoin_eq_middle D.index D.lift p.curve q.curve ⟨ht.1.le, ht.2⟩
  have hrightEq : (∫ s in (c - d)..τ₂, F s) =
      ∫ s in (c - d)..τ₂, M14BackwardLIntegrand G q s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.le
    intro s hs
    apply rawLIntegrand_eq_backward_of_eventuallyEq q ⟨(ha.trans hab).trans hs.1, hs.2⟩
    filter_upwards [lt_mem_nhds hs.1] with t ht
    exact oneSidedGaugeJoin_eq_right D.index D.lift p.curve q.curve hd hsmall hqRec ht.le
  change (∫ s in τ₁..τ₂, F s) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft (hmiddle.trans hright),
    ← intervalIntegral.integral_add_adjacent_intervals hmiddle hright,
    hleftEq, hmiddleEq, hrightEq, add_assoc]

end PoincareConjecture.M14
