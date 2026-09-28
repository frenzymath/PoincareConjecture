import PoincareConjecture.Proofs.M14.Sec6_1_PathJoining
import PoincareConjecture.Proofs.M14.Sec6_1_PathTail
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeJoinBoundary
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinCoordinates

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}

noncomputable def prefixJoinPath (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) (D : PrefixJoinGauge q p)
    (d : ℝ) (hd : 0 < d) (hsmall : 2 * d < D.radius) :
    M14BackwardPath G T τ₁ τ₂ x y := by
  let γ := oneSidedGaugeJoin D.index D.lift p.curve q.curve c D.radius d
  have hc : c < τ₂ := by linarith [D.radius_pos, D.right_margin]
  have hwide (s : ℝ) (hs : s ∈ Icc (c - D.radius) c) :
      s ∈ Icc (c - D.radius) (c + D.radius) :=
    ⟨hs.1, by linarith [hs.2, D.radius_pos]⟩
  have hpRec (s : ℝ) (hs : s ∈ Icc (c - D.radius) c) :
      (G.gaugeCover.cylinder D.index).toSpacetime (D.lift (p.curve s)) = p.curve s :=
    D.lift_right _ (D.prefix_in_image s hs)
  have hqRec (s : ℝ) (hs : s ∈ Icc (c - D.radius) c) :
      (G.gaugeCover.cylinder D.index).toSpacetime (D.lift (q.curve s)) = q.curve s :=
    D.lift_right _ (D.continuation_in_image s (hwide s hs))
  have hqReg : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 q.curve
      (Ioo (c - D.radius) τ₂) :=
    q.curve_regular.mono (Ioo_subset_Ioo D.left_margin.le le_rfl)
  have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 γ (Ioo τ₁ τ₂) :=
    oneSidedGaugeJoin_contMDiffOn D.index D.lift p.curve q.curve D.image_open D.lift_smooth
      (by simp) hd hsmall p.curve_regular hqReg D.prefix_in_image
      (fun s hs => D.continuation_in_image s (hwide s hs)) hpRec hqRec
      (fun _ hs => D.overlap_time hs)
      (fun s hs => D.region_subset (D.blend_mem_region _ _ (Ioo_subset_Icc_self hs)))
  have hcont : ContinuousOn γ (Icc τ₁ τ₂) :=
    oneSidedGaugeJoin_continuousOn D.index D.lift p.curve q.curve D.radius_pos D.left_margin hc
      p.curve_continuous (q.curve_continuous.mono (Icc_subset_Icc D.left_margin.le le_rfl))
      hreg.continuousOn
  have hclock (s : ℝ) (hs : s ∈ Icc τ₁ τ₂) : G.spacetime.timeFunction (γ s) = T - s :=
    oneSidedGaugeJoin_clock D.index D.lift p.curve q.curve D.radius_pos (fun t => T - t)
      p.curve_time (fun t ht => q.curve_time t ⟨D.left_margin.le.trans ht.1, ht.2⟩) hqRec hs
  exact pathOfC1Join hM12 p (tailPath q c p.tau_lt.le hc) γ (a := c - 2 * d) (b := c + d)
    (by linarith [D.left_margin]) (by linarith) (by linarith)
    (by linarith [D.right_margin]) hcont hreg hclock
    (fun t ht => oneSidedGaugeJoin_eq_left D.index D.lift p.curve q.curve hd hpRec
      (fun _ hs => D.overlap_time hs) ht)
    (fun t ht => oneSidedGaugeJoin_eq_right D.index D.lift p.curve q.curve hd hsmall hqRec
      (by linarith))

theorem prefixJoinPath_curve (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) (D : PrefixJoinGauge q p)
    (d : ℝ) (hd : 0 < d) (hsmall : 2 * d < D.radius) :
    (prefixJoinPath hM12 q p D d hd hsmall).curve =
      oneSidedGaugeJoin D.index D.lift p.curve q.curve c D.radius d := rfl

theorem action_prefixJoinPath (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) (D : PrefixJoinGauge q p)
    (d : ℝ) (hd : 0 < d) (hsmall : 2 * d < D.radius) :
    M14BackwardLAction G (prefixJoinPath hM12 q p D d hd hsmall) =
      (∫ t in τ₁..(c - 2 * d), M14BackwardLIntegrand G p t) +
        (∫ t in (c - 2 * d)..(c + d),
          M14BackwardLIntegrand G (prefixJoinPath hM12 q p D d hd hsmall) t) +
        ∫ t in (c + d)..τ₂, M14BackwardLIntegrand G q t := by
  dsimp only [prefixJoinPath]
  rw [action_pathOfC1Join]
  rfl

end PoincareConjecture.M14
