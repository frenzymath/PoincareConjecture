import PoincareConjecture.Proofs.M47.LimitFiniteCapDistance
import PoincareConjecture.Proofs.M47.LimitFiniteBallEndpoint
import PoincareConjecture.Proofs.M47.TerminalRegularFiniteCapBudget










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : ℕ → SurgeryFlowData.{u}} (index : ℕ → ℕ)
  (base Q : ℕ → ℝ)
  {C : GeneralizedSliceCarrier.{u}}
  (g : RiemannianMetric 3 C.carrier) (o : C.carrier) (R : ℝ)

private local instance uniformCapTopology : TopologicalSpace C.carrier :=
  C.topologicalSpace
private local instance uniformCapCharts : ChartedSpace E C.carrier := C.chartedSpace
private local instance uniformCapManifold : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold




theorem limitFinite_uniform_cap_exclusion
    {c d window Bplus D : ℝ}
    (P : M47Predecessors.{u})
    (hQ : ∀ k, 0 < Q (index k))
    (hR : 0 < R) (hcneg : c < 0) (_hd : 0 < d)
    (_hwindow : 0 ≤ window) (hbuffer : -window ≤ c - 4 * d)
    (hBplus : 0 ≤ Bplus)
    (hDformula : D = 2 * Real.sqrt (2 * Real.exp (6 * Bplus * window)) * R)
    (_hD : 0 < D)
    (hpinch : ∀ k, SurgeryFlowPinched (F (index k)))
    (badPoint : ∀ k, ((F (index k)).slice (base (index k))).carrier)
    (hbad : ∀ k, ¬ SurgeryCanonicalControl (F (index k)) (base (index k))
      (badPoint k) (F (index k)).parameters.epsilon (F (index k)).parameters.C)
    (hscalarBad : ∀ k, ((F (index k)).connection (base (index k))).scalarCurvature
      (badPoint k) = Q (index k))
    (Retain : ∀ k (b : ℝ),
      SurgeryFlowCylinder (F (index k)) C (base (index k)) (Q (index k))
        (Icc b 0) (g.ball o R) → Prop)
    (hsearch : ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      ∃ b, ∃ hb : b ∈ Icc (c - 4 * d) c,
        ∃ E0 : SurgeryFlowCylinder (F (index k)) C (base (index k))
            (Q (index k)) (Icc b 0) (g.ball o R),
          Retain k b E0 ∧
          (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ g.ball o R,
            |((F (index k)).connection (base (index k) + s / Q (index k))).curvatureTensorNorm
                (E0.forward s hs x)| ≤ Bplus * Q (index k) ∧
            ((F (index k)).connection (base (index k) + s / Q (index k))).negativeCurvaturePart
                (E0.forward s hs x) ≤ eta * Q (index k)) ∧
          (∀ x ∈ g.ball o R, ∀ v : TangentSpace (𝓡 3) x,
            E0.pullbackInner 0 ⟨hb.2.trans hcneg.le, le_rfl⟩ x v v ≤ 2 * g.inner x v v) ∧
          ((⟨base (index k) + 0 / Q (index k),
              E0.forward 0 ⟨hb.2.trans hcneg.le, le_rfl⟩ o⟩ :
              Σ t, ((F (index k)).slice t).carrier) =
            ⟨base (index k), badPoint k⟩) ∧
          (b < c - 2 * d ∨
            ∃ hEvent : base (index k) + b / Q (index k) ∈ (F (index k)).surgery_times,
              ∀ [Nonempty ((F (index k)).slice
                (base (index k) + b / Q (index k))).carrier],
                ∃ i : Fin ((F (index k)).event
                    (base (index k) + b / Q (index k)) hEvent).cap_count,
                  Set.Nonempty (E0.forward b ⟨le_rfl, hb.2.trans hcneg.le⟩ '' g.ball o R ∩
                    (((F (index k)).event
                      (base (index k) + b / Q (index k)) hEvent).caps i).carrier)))
    (capBudget : ∀ j : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
      ∀ E0 : SurgeryFlowCylinder (F (index k)) C (base (index k))
          (Q (index k)) (Icc a 0) (g.ball o R),
        (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ g.ball o R,
          ((F (index k)).connection (base (index k) + s / Q (index k))).scalarCurvature
              (E0.forward s hs x) ≤ ((j : ℝ) + 1) * Q (index k)) →
        ∀ (hEvent : base (index k) + a / Q (index k) ∈ (F (index k)).surgery_times),
        ∀ [Nonempty ((F (index k)).slice
          (base (index k) + a / Q (index k))).carrier],
        ∀ (i : Fin ((F (index k)).event
            (base (index k) + a / Q (index k)) hEvent).cap_count)
          (contact : C.carrier),
          contact ∈ g.ball o R →
          E0.forward a ⟨le_rfl, ha.2.le⟩ contact ∈
            (((F (index k)).event
              (base (index k) + a / Q (index k)) hEvent).caps i).carrier →
          (∀ x ∈ g.ball o R,
            ((F (index k)).metric (base (index k) + a / Q (index k))).edist
              (E0.forward a ⟨le_rfl, ha.2.le⟩ contact)
              (E0.forward a ⟨le_rfl, ha.2.le⟩ x) ≤
                ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (Q (index k)))) →
          ∀ y ∈ g.ball o R,
            ((F (index k)).connection (base (index k) + 0 / Q (index k))).scalarCurvature
                (E0.forward 0 ⟨ha.2.le, le_rfl⟩ y) = Q (index k) →
            SurgeryCanonicalControl (F (index k))
              (base (index k) + 0 / Q (index k))
              (E0.forward 0 ⟨ha.2.le, le_rfl⟩ y)
              (F (index k)).parameters.epsilon (F (index k)).parameters.C) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
      ∃ b, ∃ hb : b ∈ Icc (c - 4 * d) c,
        ∃ E0 : SurgeryFlowCylinder (F (index k)) C (base (index k))
            (Q (index k)) (Icc b 0) (g.ball o R),
          Retain k b E0 ∧
          (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ g.ball o R,
            |((F (index k)).connection (base (index k) + s / Q (index k))).curvatureTensorNorm
                (E0.forward s hs x)| ≤ Bplus * Q (index k) ∧
            ((F (index k)).connection (base (index k) + s / Q (index k))).negativeCurvaturePart
                (E0.forward s hs x) ≤ eta * Q (index k)) ∧
          (∀ x ∈ g.ball o R, ∀ v : TangentSpace (𝓡 3) x,
            E0.pullbackInner 0 ⟨hb.2.trans hcneg.le, le_rfl⟩ x v v ≤ 2 * g.inner x v v) ∧
          ((⟨base (index k) + 0 / Q (index k),
              E0.forward 0 ⟨hb.2.trans hcneg.le, le_rfl⟩ o⟩ :
              Σ t, ((F (index k)).slice t).carrier) =
            ⟨base (index k), badPoint k⟩) ∧ b < c - 2 * d := by
  have hU : IsOpen (g.ball o R) := M04.initial_ball_isOpen g o R
  have ho : o ∈ g.ball o R := by
    change g.edist o o < ENNReal.ofReal R
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hR
  obtain ⟨j, hj⟩ := exists_nat_ge (max (window + 1) (max (3 * Bplus) D))
  have hjWindow : window ≤ (j : ℝ) + 1 := by
    linarith only [le_max_left (window + 1) (max (3 * Bplus) D), hj]
  have hjScalar : 3 * Bplus ≤ (j : ℝ) + 1 := by
    linarith only [le_max_right (window + 1) (max (3 * Bplus) D),
      le_max_left (3 * Bplus) D, hj]
  have hjDistance : D ≤ (j : ℝ) + 1 := by
    linarith only [le_max_right (window + 1) (max (3 * Bplus) D),
      le_max_right (3 * Bplus) D, hj]
  intro eta heta
  filter_upwards [hsearch eta heta, capBudget j] with k hk hcapBudget
  obtain ⟨b, hb, E0, hretain, hbounds, hzeroInner, hpoint, hstop⟩ := hk
  have hQk : 0 < Q (index k) := hQ k
  have hage : b ∈ Icc (-window) 0 := by
    constructor
    · linarith only [hb.1, hbuffer]
    · exact hb.2.trans hcneg.le
  have hb0 : b ≤ 0 := hb.2.trans hcneg.le
  have hK : 0 ≤ Bplus := hBplus
  have hRm : ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ g.ball o R,
      ((F (index k)).connection (base (index k) + s / Q (index k))).curvatureTensorNorm
        (E0.forward s hs x) ≤ Bplus * Q (index k) := by
    intro s hs x hx
    exact (le_abs_self _).trans (hbounds s hs x hx).1
  let P44 : M44CapPersistencePredecessors.{u} :=
    ⟨P.m04, P.m13.ordinary_flow⟩
  have hdist := finite_source_ball_bottom_distance
    P44 (hpinch k) g o hR hK hage E0 hRm hzeroInner
  refine ⟨b, hb, E0, hretain, hbounds, hzeroInner, hpoint, ?_⟩
  rcases hstop with hlong | hcap
  · exact hlong
  · exfalso
    obtain ⟨hEvent, hcap⟩ := hcap
    let : Nonempty ((F (index k)).slice
        (base (index k) + b / Q (index k))).carrier :=
      ⟨E0.forward b ⟨le_rfl, hb0⟩ o⟩
    obtain ⟨i, contact, hzimage, hzcap⟩ := hcap
    obtain ⟨contact, hcontact, rfl⟩ := hzimage
    have hscalar : ∀ s (hs : s ∈ Icc b 0), ∀ x ∈ g.ball o R,
        ((F (index k)).connection (base (index k) + s / Q (index k))).scalarCurvature
        (E0.forward s hs x) ≤ ((j : ℝ) + 1) * Q (index k) := by
      intro s hs x hx
      have hnorm := (le_abs_self _).trans (hbounds s hs x hx).1
      calc
        _ ≤ 3 * ((F (index k)).connection (base (index k) + s / Q (index k))).curvatureTensorNorm
            (E0.forward s hs x) :=
          (((F (index k)).connection
              (base (index k) + s / Q (index k))).scalarCurvature_le_curvatureTensorNorm_sharp _)
        _ ≤ 3 * (Bplus * Q (index k)) :=
          mul_le_mul_of_nonneg_left hnorm (by norm_num)
        _ ≤ (3 * Bplus) * Q (index k) := by
          simpa only [mul_assoc] using
            (le_refl (3 * (Bplus * Q (index k))))
        _ ≤ ((j : ℝ) + 1) * Q (index k) := by
          exact mul_le_mul_of_nonneg_right hjScalar hQk.le
    have hdist' : ∀ x ∈ g.ball o R,
        ((F (index k)).metric (base (index k) + b / Q (index k))).edist
            (E0.forward b ⟨le_rfl, hb0⟩ contact)
            (E0.forward b ⟨le_rfl, hb0⟩ x) ≤
          ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (Q (index k))) := by
      intro x hx
      have hd0 := hdist contact hcontact x hx
      have hdD :
          ((F (index k)).metric (base (index k) + b / Q (index k))).edist
              (E0.forward b ⟨le_rfl, hb0⟩ contact)
              (E0.forward b ⟨le_rfl, hb0⟩ x) ≤
            ENNReal.ofReal (D / Real.sqrt (Q (index k))) := by
        simpa only [hDformula] using hd0
      apply hdD.trans
      apply ENNReal.ofReal_mono
      exact div_le_div_of_nonneg_right hjDistance (Real.sqrt_nonneg _)
    have hscalarPoint :
        ((F (index k)).connection (base (index k) + 0 / Q (index k))).scalarCurvature
            (E0.forward 0 ⟨hb0, le_rfl⟩ o) = Q (index k) := by
      exact (congrArg (fun z : Σ t, ((F (index k)).slice t).carrier =>
        ((F (index k)).connection z.1).scalarCurvature z.2) hpoint).trans
        (hscalarBad k)
    have hcontrol := hcapBudget (ha := by
      constructor
      · linarith only [hb.1, hbuffer, hjWindow]
      · exact lt_of_le_of_lt hb.2 hcneg) E0 hscalar hEvent i contact hcontact hzcap hdist'
      o ho hscalarPoint
    have hbadControl := (congrArg
      (fun z : Σ t, ((F (index k)).slice t).carrier =>
        SurgeryCanonicalControl (F (index k)) z.1 z.2
          (F (index k)).parameters.epsilon (F (index k)).parameters.C) hpoint).mp hcontrol
    exact hbad k hbadControl

end PoincareConjecture.M47
