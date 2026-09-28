import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RadiusSelection
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Distance








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace Poincare.CurvatureIntegral

variable {X : Type*} [MetricSpace X]


theorem HasLocalDistanceAscent.mono {c c' : ℝ} {p y : X}
    (h : HasLocalDistanceAscent c' p y) (hcc' : c ≤ c') :
    HasLocalDistanceAscent c p y := by
  intro s hs
  obtain ⟨z, hz, hgain⟩ := h s hs
  exact ⟨z, hz, (mul_le_mul_of_nonneg_right hcc' dist_nonneg).trans_lt hgain⟩


theorem HasLocalDistanceAscent.of_subtype {U : Set X} {c : ℝ} {p y : U}
    (h : HasLocalDistanceAscent c p y) :
    HasLocalDistanceAscent c p.val y.val := by
  intro s hs
  obtain ⟨z, hz, hgain⟩ := h s hs
  exact ⟨z.val, hz, hgain⟩


theorem hasLocalDistanceAscent_subtype_iff {U : Set X} (hU : IsOpen U)
    (c : ℝ) (p y : U) :
    HasLocalDistanceAscent c p y ↔ HasLocalDistanceAscent c p.val y.val := by
  refine ⟨HasLocalDistanceAscent.of_subtype, ?_⟩
  intro h s hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y.val y.property
  obtain ⟨z, hz, hgain⟩ := h (min s ε) (lt_min hs hε)
  have hzU : z ∈ U := hball (by
    rw [Metric.mem_ball, dist_comm]
    exact hz.trans_le (min_le_right _ _))
  exact ⟨⟨z, hzU⟩, hz.trans_le (min_le_left _ _), hgain⟩


theorem hasLocalDistanceAscent_ballModel_iff
    (X : Poincare.GromovHausdorff.BasedMetricSpaceBundle) {L : ℝ} (hL : 0 < L)
    (c : ℝ) (p y : (Poincare.GromovHausdorff.ballModel X L hL).carrier) :
    HasLocalDistanceAscent c p y ↔ HasLocalDistanceAscent c p.val y.val :=
  hasLocalDistanceAscent_subtype_iff Metric.isOpen_ball c p y

end Poincare.CurvatureIntegral

namespace Poincare.GromovHausdorff



theorem isCompact_closedBall_ballModel
    (X : BasedMetricSpaceBundle) [ProperSpace X.carrier]
    {L : ℝ} (hL : 0 < L) (x : (ballModel X L hL).carrier) {δ : ℝ}
    (hroom : dist X.base x.val + δ < L) :
    IsCompact (Metric.closedBall x δ) := by
  apply Subtype.isCompact_iff.mpr
  have himage : (Subtype.val : (ballModel X L hL).carrier → X.carrier) ''
      Metric.closedBall x δ = Metric.closedBall x.val δ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      have hdist : dist x.val z ≤ δ := by
        simpa only [Metric.mem_closedBall, dist_comm] using hz
      have hzball : z ∈ Metric.ball X.base L := by
        rw [Metric.mem_ball, dist_comm]
        exact (dist_triangle X.base x.val z).trans_lt
          ((add_le_add le_rfl hdist).trans_lt hroom)
      exact ⟨⟨z, hzball⟩, hz, rfl⟩
  rw [himage]
  exact isCompact_closedBall x.val δ

end Poincare.GromovHausdorff
