import PoincareConjecture.Proofs.M38.StandardCapBall
import PoincareConjecture.Proofs.M38.RadialCoordinates
import PoincareConjecture.Proofs.M38.LocalEmbedding
import PoincareConjecture.Proofs.M38.SmoothChart
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

theorem standard_cap_ball_extended (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r) :
    Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) := by
  have hclosed : closure (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) ⊆
      {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)} := by
    apply closure_minimal ?_ (standard_closed_ball_closed _ _)
    exact fun x hx => (show g₀.metric.edist 0 x <
      ENNReal.ofReal (g₀.cylindrical_end.radius + 4) from hx).le
  rw [hball, closure_ball _ hr.ne'] at hclosed
  intro x hx
  exact (hclosed hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
    linarith [g₀.cylindrical_end.radius_pos])).mpr (by linarith))

theorem exists_cap_ball_width {r : ℝ} (hr : 0 < r) {U : Set StandardCapSpace}
    (hU : IsOpen U) (hsub : Metric.closedBall 0 r ⊆ U) :
    ∃ c : ℝ, 0 < c ∧ c < r ∧ Metric.ball 0 (r + c) ⊆ U := by
  have hcompact := isCompact_closedBall (0 : StandardCapSpace) r
  obtain ⟨d, hd, hthick⟩ := hcompact.exists_thickening_subset_open hU hsub
  rw [thickening_closedBall hd hr.le] at hthick
  obtain ⟨c, hc, hcmin⟩ := exists_between (lt_min hd hr)
  refine ⟨c, hc, hcmin.trans_le (min_le_right d r), ?_⟩
  exact Set.Subset.trans
    (Metric.ball_subset_ball (by linarith [hcmin.trans_le (min_le_left d r)])) hthick

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)

noncomputable def eventCapBall (r c : ℝ) (hc : 0 < c) (hcr : c < r)
    (hdom : Metric.ball (0 : StandardCapSpace) (r + c) ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5)) :
    SurgeryBallEmbedding (F.slice T) := by
  let X := capRadialDiffeomorph r c hc hcr
  let R := (F.event T hT).local_result i
  let e := (F.event T hT).local_embed i
  let f : StandardCapSpace → (F.slice T).carrier := fun x => e (R.cap_map (X x))
  let g : (F.slice T).carrier → StandardCapSpace :=
    fun y => X.symm (R.cap_inverse (localEmbedInverse F T hT i y))
  have hX : Set.MapsTo X (Metric.ball 0 2)
      (F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5)) := by
    intro x hx
    apply hdom
    rw [← capRadialDiffeomorph_ball_two hc hcr]
    exact Set.mem_image_of_mem X hx
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    ((F.event T hT).local_embed_smooth i).comp_contMDiffOn
      (R.cap_map_smooth.comp X.contMDiff.contMDiffOn hX)
  have hleft : Set.LeftInvOn g f (Metric.ball 0 2) := by
    intro x hx
    change X.symm (R.cap_inverse (localEmbedInverse F T hT i (e (R.cap_map (X x))))) = x
    rw [local_embed_left_inverse F T hT i, R.cap_left_inverse (hX hx), X.symm_apply_apply]
  have hlocal : f '' Metric.ball 0 2 ⊆ Set.range e := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨R.cap_map (X x), rfl⟩
  have himage : Set.MapsTo (localEmbedInverse F T hT i) (f '' Metric.ball 0 2)
      (R.cap_map '' F.standard_initial.metric.ball 0
        (F.standard_initial.cylindrical_end.radius + 5)) := by
    rintro _ ⟨x, hx, rfl⟩
    change localEmbedInverse F T hT i (e (R.cap_map (X x))) ∈ _
    rw [local_embed_left_inverse F T hT i]
    exact Set.mem_image_of_mem R.cap_map (hX hx)
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    X.symm.contMDiff.comp_contMDiffOn (R.cap_inverse_smooth.comp
      ((local_embed_inverse_smooth F T hT i).mono hlocal) himage)
  exact {
    map := f
    inverse := g
    map_smooth := hf
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg f (hleft hx)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball hf hg hleft }

theorem eventCapBall_map (r c : ℝ) (hc : 0 < c) (hcr : c < r)
    (hdom : Metric.ball (0 : StandardCapSpace) (r + c) ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5))
    (x : StandardCapSpace) :
    (eventCapBall F T hT i r c hc hcr hdom).map x =
      (F.event T hT).local_embed i (((F.event T hT).local_result i).cap_map
        (capRadialDiffeomorph r c hc hcr x)) := rfl

theorem eventCapBall_closedBall (r c : ℝ) (hc : 0 < c) (hcr : c < r)
    (hdom : Metric.ball (0 : StandardCapSpace) (r + c) ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5))
    (hcap : (F.event T hT).local_embed i ''
      (((F.event T hT).local_result i).cap_map '' Metric.closedBall 0 r) =
        ((F.event T hT).caps i).carrier) :
    (eventCapBall F T hT i r c hc hcr hdom).closedBall =
      ((F.event T hT).caps i).carrier := by
  change ((F.event T hT).local_embed i ∘ ((F.event T hT).local_result i).cap_map ∘
    capRadialDiffeomorph r c hc hcr) '' Metric.closedBall 0 1 = _
  rw [Set.image_comp, Set.image_comp, capRadialDiffeomorph_closedBall hc hcr]
  exact hcap

theorem exists_event_cap_ball : ∃ B : SurgeryBallEmbedding (F.slice T),
    B.closedBall = ((F.event T hT).caps i).carrier ∧ B.map 0 = ((F.event T hT).caps i).tip := by
  obtain ⟨r, hr, hball, hcap⟩ := event_cap_euclidean_radius F T hT i
  obtain ⟨c, hc, hcr, hdom⟩ := exists_cap_ball_width hr (standard_ball_open _ _)
    (standard_cap_ball_extended _ hr hball)
  refine ⟨eventCapBall F T hT i r c hc hcr hdom,
    eventCapBall_closedBall F T hT i r c hc hcr hdom hcap, ?_⟩
  rw [eventCapBall_map]
  change (F.event T hT).local_embed i (((F.event T hT).local_result i).cap_map
    (capRadialMap (capRadialOrderIso r c hc hcr) 0)) = _
  rw [capRadialMap_zero, ((F.event T hT).local_result i).cap_map_tip,
    (F.event T hT).local_tip]

end PoincareConjecture.M38
