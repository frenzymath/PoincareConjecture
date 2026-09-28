import PoincareConjecture.Proofs.M47.FiniteHorizonCapContradiction
import PoincareConjecture.Proofs.M47.LimitCapSourceDistance
import PoincareConjecture.Proofs.M47.BlowupControlsPinching
import PoincareConjecture.Proofs.M47.SeedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (base Q : ℕ → ℝ)
  {C : GeneralizedSliceCarrier.{u}} (g : RiemannianMetric 3 C.carrier) (o : C.carrier)
  (terminal : ∀ k, C.carrier → ((F k).slice (base k + 0 / Q k)).carrier)
  (badPoint : ∀ k, ((F k).slice (base k)).carrier)

def FiniteHorizonCapCylinderContact (c d : ℝ) (hc : c < 0) (k : ℕ) (R : ℝ) : Prop :=
  ∃ (a : ℝ) (ha : a ∈ Icc (c - 4 * d) c),
    ∃ E : SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc a 0) (g.ball o R),
      (∀ hz : (0 : ℝ) ∈ Icc a 0, ∀ x ∈ g.ball o R,
        E.forward 0 hz x = terminal k x) ∧
      (∀ x ∈ g.ball o R, ∀ v : TangentSpace (𝓡 3) x,
        E.pullbackInner 0 ⟨ha.2.trans hc.le, le_rfl⟩ x v v ≤ 2 * g.inner x v v) ∧
      ((⟨base k + 0 / Q k, E.forward 0 ⟨ha.2.trans hc.le, le_rfl⟩ o⟩ :
          Σ t, ((F k).slice t).carrier) = ⟨base k, badPoint k⟩) ∧
      ∃ hEvent : base k + a / Q k ∈ (F k).surgery_times,
        ∀ [Nonempty ((F k).slice (base k + a / Q k)).carrier],
          ∃ i : Fin ((F k).event (base k + a / Q k) hEvent).cap_count,
            Set.Nonempty (E.forward a ⟨le_rfl, ha.2.trans hc.le⟩ '' g.ball o R ∩
              (((F k).event (base k + a / Q k) hEvent).caps i).carrier)

theorem finiteHorizon_no_frequent_cap_of_scalar_service
    (P : M47Predecessors.{u}) {c d K : ℝ} (hc : c < 0) (hK : 0 ≤ K)
    (hQ : ∀ k, 0 < Q k) (hDiverges : Tendsto Q atTop atTop)
    (hPinched : ∀ k, SurgeryFlowPinched (F k))
    (hScalarBad : ∀ k, ((F k).connection (base k)).scalarCurvature (badPoint k) = Q k)
    (hbad : ∀ k, ¬ SurgeryCanonicalControl (F k) (base k) (badPoint k)
      (F k).parameters.epsilon (F k).parameters.C)
    (scalarService : ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      ∀ (a : ℝ) (_ha : a ∈ Icc (c - 4 * d) c),
      ∀ E : SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc a 0) (g.ball o R),
        (∀ hz : (0 : ℝ) ∈ Icc a 0, ∀ x ∈ g.ball o R,
          E.forward 0 hz x = terminal k x) →
        ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
          ((F k).connection (base k + s / Q k)).scalarCurvature
            (E.forward s hs x) ≤ K * Q k)
    (capBudget : ∀ j : ℕ, ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
      ∀ E : SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc a 0) (g.ball o R),
        (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
          ((F k).connection (base k + s / Q k)).scalarCurvature
            (E.forward s hs x) ≤ ((j : ℝ) + 1) * Q k) →
        ∀ (hEvent : base k + a / Q k ∈ (F k).surgery_times),
        ∀ [Nonempty ((F k).slice (base k + a / Q k)).carrier],
        ∀ (i : Fin ((F k).event (base k + a / Q k) hEvent).cap_count) (contact : C.carrier),
          contact ∈ g.ball o R →
          E.forward a ⟨le_rfl, ha.2.le⟩ contact ∈
            (((F k).event (base k + a / Q k) hEvent).caps i).carrier →
          (∀ x ∈ g.ball o R, ((F k).metric (base k + a / Q k)).edist
            (E.forward a ⟨le_rfl, ha.2.le⟩ contact) (E.forward a ⟨le_rfl, ha.2.le⟩ x) ≤
              ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (Q k))) →
          ∀ y ∈ g.ball o R,
            ((F k).connection (base k + 0 / Q k)).scalarCurvature
              (E.forward 0 ⟨ha.2.le, le_rfl⟩ y) = Q k →
            SurgeryCanonicalControl (F k) (base k + 0 / Q k)
              (E.forward 0 ⟨ha.2.le, le_rfl⟩ y)
              (F k).parameters.epsilon (F k).parameters.C) :
    ¬ ∃ R : ℝ, 0 < R ∧ ∃ᶠ k : ℕ in atTop,
      FiniteHorizonCapCylinderContact F base Q g o terminal badPoint c d hc k R := by
  intro contacts
  let LineBound : ℕ → ℝ → Prop := fun k R =>
    ∀ (a : ℝ) (_ha : a ∈ Icc (c - 4 * d) c),
    ∀ E : SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc a 0) (g.ball o R),
      (∀ hz : (0 : ℝ) ∈ Icc a 0, ∀ x ∈ g.ball o R,
        E.forward 0 hz x = terminal k x) →
      ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
        ((F k).connection (base k + s / Q k)).scalarCurvature
          (E.forward s hs x) ≤ K * Q k
  apply finiteHorizon_cap_persistence_contradiction
    (Contact := FiniteHorizonCapCylinderContact F base Q g o terminal badPoint c d hc)
    (LineBound := LineBound)
    (Canonical := fun k _ => SurgeryCanonicalControl (F k) (base k) (badPoint k)
      (F k).parameters.epsilon (F k).parameters.C)
    (fun k _ => hbad k) contacts
  · intro R hR
    exact (scalarService R hR).mono (fun _ bound _ => bound)
  · intro R hR
    let Knorm := 13 * max K 1
    have hKnorm : 0 ≤ Knorm := by
      dsimp only [Knorm]
      positivity
    let window := -c + 4 * d
    let D := 2 * Real.sqrt (2 * Real.exp (6 * Knorm * window)) * R
    obtain ⟨j, hj⟩ := exists_nat_ge (max (window + 1) (max K D))
    have hjWindow : window ≤ (j : ℝ) + 1 := by
      linarith only [le_max_left (window + 1) (max K D), hj]
    have hjScalar : K ≤ (j : ℝ) + 1 := by
      linarith only [le_max_right (window + 1) (max K D), le_max_left K D, hj]
    have hjDistance : D ≤ (j : ℝ) + 1 := by
      linarith only [le_max_right (window + 1) (max K D), le_max_right K D, hj]
    have ho : o ∈ g.ball o R := by
      change g.edist o o < ENNReal.ofReal R
      rw [M36.metric_edist_self]
      exact ENNReal.ofReal_pos.mpr hR
    filter_upwards [capBudget j R hR,
      hDiverges.eventually (eventually_ge_atTop (blowupPinchingThreshold K 1))]
      with k hbudget hscale
    intro contact hline
    obtain ⟨a, ha, E, hzero, hquadratic, hpoint, hEvent, hcap⟩ := contact
    have ha0 : a ≤ 0 := ha.2.trans hc.le
    have hscalar := hline a ha E hzero
    have hnorm : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
        ((F k).connection (base k + s / Q k)).curvatureTensorNorm
          (E.forward s hs x) ≤ Knorm * Q k := by
      intro s hs x hx
      have hbound := pinched_blowup_curvature_bounds P.toM46
        (hPinched k _ (E.time_subset (mem_image_of_mem _ hs))) hK zero_lt_one hscale
        (mem_univ _) (hscalar s hs x hx)
      exact (le_abs_self _).trans hbound.1
    have hage : a ∈ Icc (-window) 0 := by
      dsimp only [window]
      exact ⟨by linarith only [ha.1], ha0⟩
    have hdist := finite_source_ball_bottom_distance
      (P := ⟨P.m04, P.m13.ordinary_flow⟩) (hPinched k) g o hR hKnorm hage E hnorm hquadratic
    let : Nonempty ((F k).slice (base k + a / Q k)).carrier :=
      ⟨E.forward a ⟨le_rfl, ha0⟩ o⟩
    obtain ⟨i, imagePoint, hImage, hCap⟩ := hcap
    obtain ⟨contactPoint, hContact, rfl⟩ := hImage
    have hageBudget : a ∈ Ico (-((j : ℝ) + 1)) 0 := by
      constructor
      · linarith only [hage.1, hjWindow]
      · exact ha.2.trans_lt hc
    have hscalarBudget : ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
        ((F k).connection (base k + s / Q k)).scalarCurvature
          (E.forward s hs x) ≤ ((j : ℝ) + 1) * Q k := by
      intro s hs x hx
      exact (hscalar s hs x hx).trans
        (mul_le_mul_of_nonneg_right hjScalar (hQ k).le)
    have hdistBudget : ∀ x ∈ g.ball o R,
        ((F k).metric (base k + a / Q k)).edist
          (E.forward a ⟨le_rfl, ha0⟩ contactPoint) (E.forward a ⟨le_rfl, ha0⟩ x) ≤
            ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (Q k)) := by
      intro x hx
      exact (hdist contactPoint hContact x hx).trans (ENNReal.ofReal_mono
        (div_le_div_of_nonneg_right hjDistance (Real.sqrt_nonneg (Q k))))
    have hscalarPoint : ((F k).connection (base k + 0 / Q k)).scalarCurvature
        (E.forward 0 ⟨ha0, le_rfl⟩ o) = Q k :=
      (congrArg (fun z : Σ t, ((F k).slice t).carrier =>
        ((F k).connection z.1).scalarCurvature z.2) hpoint).trans (hScalarBad k)
    have hcanonical := hbudget hageBudget E hscalarBudget hEvent i
      contactPoint hContact hCap hdistBudget o ho hscalarPoint
    exact (congrArg (fun z : Σ t, ((F k).slice t).carrier =>
      SurgeryCanonicalControl (F k) z.1 z.2 (F k).parameters.epsilon
        (F k).parameters.C) hpoint).mp hcanonical

end PoincareConjecture.M47
