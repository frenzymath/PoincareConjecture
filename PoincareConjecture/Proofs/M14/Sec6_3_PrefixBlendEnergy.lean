import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinGauge
import PoincareConjecture.Proofs.M14.Sec6_1_GaugeEnergy
import PoincareConjecture.Proofs.M14.Mathlib.BlendEnergyLimit









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

universe u

namespace PoincareConjecture.M14.PrefixJoinGauge

open Proofs.M09

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}
  {q : M14BackwardPath G T τ₁ τ₂ x y}
  {p : M14BackwardPath G T τ₁ c x (q.curve c)} (D : PrefixJoinGauge q p)




theorem blend_energy_properties (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    let f := fun s => (D.lift (p.curve s)).2.val
    let g := fun s => (D.lift (q.curve s)).2.val
    (∀ d : ℝ, 0 < d → 2 * d < D.radius →
      IntervalIntegrable
        (fun s => ‖deriv (smoothJoinBlend f g (c - 3 * d / 2) (d / 2)) s‖ ^ 2)
        volume (c - 2 * d) (c - d)) ∧
    Tendsto (fun d => ∫ s in (c - 2 * d)..(c - d),
      ‖deriv (smoothJoinBlend f g (c - 3 * d / 2) (d / 2)) s‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  dsimp only
  have hpos : 0 < c - D.radius := p.tau_nonneg.trans_lt D.left_margin
  have hlt : c - D.radius < c := by linarith [D.radius_pos]
  have hp := backwardPath_gauge_derivative_memLp p D.index D.lift hM12
    D.lift_smooth D.lift_right hpos hlt D.left_margin.le le_rfl D.prefix_in_image
  have hq := backwardPath_gauge_derivative_memLp q D.index D.lift hM12
    D.lift_smooth D.lift_right hpos hlt D.left_margin.le
    (by linarith [D.radius_pos, D.right_margin])
    (fun s hs => D.continuation_in_image s ⟨hs.1, by linarith [hs.2, D.radius_pos]⟩)
  have hdp : DifferentiableOn ℝ (fun s => (D.lift (p.curve s)).2.val)
      (Ioo (c - D.radius) c) :=
    fun s hs => (hp.2.1 s hs).differentiableAt.differentiableWithinAt
  have hdq : DifferentiableOn ℝ (fun s => (D.lift (q.curve s)).2.val)
      (Ioo (c - D.radius) c) :=
    fun s hs => (hq.2.1 s hs).differentiableAt.differentiableWithinAt
  have heq : (D.lift (p.curve c)).2.val = (D.lift (q.curve c)).2.val := by
    rw [p.curve_end]
  refine ⟨?_, tendsto_oneSidedBlend_energy_zero hlt hp.1 hq.1 hdp hdq hp.2.2 hq.2.2 heq⟩
  intro d hd hsmall
  obtain ⟨K, hK, hKb⟩ := exists_smoothJoinCutoff_deriv_bound
  have hleft : c - D.radius ≤ c - 2 * d := by linarith
  have hsub : Icc (c - 2 * d) c ⊆ Icc (c - D.radius) c := Icc_subset_Icc hleft le_rfl
  exact (oneSidedBlend_energy_le hd hK hKb (hp.1.mono hsub) (hq.1.mono hsub)
    (hdp.mono (Ioo_subset_Ioo hleft le_rfl)) (hdq.mono (Ioo_subset_Ioo hleft le_rfl))
    (hp.2.2.mono_measure (Measure.restrict_mono hsub le_rfl))
    (hq.2.2.mono_measure (Measure.restrict_mono hsub le_rfl)) heq).1

end PoincareConjecture.M14.PrefixJoinGauge
