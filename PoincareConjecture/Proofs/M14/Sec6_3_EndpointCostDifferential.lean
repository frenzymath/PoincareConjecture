import PoincareConjecture.Proofs.M14.Sec6_3_EndpointCost
import PoincareConjecture.Proofs.M09.ShiftedCostDifferential










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

universe u

namespace PoincareConjecture.M14.GaugeEndpointFamily

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {f : ℝ × ℝ → G.Point} {U : Set ℝ} {T b c : ℝ}
  {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j}
  (D : GaugeEndpointFamily f U T 0 b c 0 j lift)




theorem cost_first_derivatives (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 b) (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hprefix : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ w : ℝ × EuclideanSpace ℝ (Fin n),
      fderiv ℝ D.prefixAction (r, (lift (f (c, r))).2.val) w = P r w.2) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      fderiv ℝ D.cost (r, 0) (1, 0) =
        (P r + fderiv ℝ D.tailAction (lift (f (c, r))).2.val)
          (deriv (fun t => (lift (f (c, t))).2.val) r) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), fderiv ℝ D.cost (r, 0) (0, v) =
        (P r + fderiv ℝ D.tailAction (lift (f (c, r))).2.val) v := by
  let a := fun r => (lift (f (c, r))).2.val
  have ha : ∀ᶠ r in 𝓝 (0 : ℝ), DifferentiableAt ℝ a r :=
    ((D.coordinate_smooth.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by simp))
  have hfixed : ∀ᶠ r in 𝓝 (0 : ℝ), (0, a r) ∈ D.parameters :=
    (continuousAt_const.prodMk D.coordinate_smooth.continuousAt).preimage_mem_nhds
      (D.parameters_open.mem_nhds D.center_mem)
  filter_upwards [D.diagonal_eventually_mem, hfixed, ha, hprefix] with r hr hrf hra hp
  have hL := (D.prefixAction_contDiffAt hM12 hc hr).differentiableAt (by simp)
  have hS := (D.tailAction_contDiffAt hM12 hc hrf).differentiableAt (by simp)
  have hform (w : ℝ × EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ D.cost (r, 0) w =
        (P r + fderiv ℝ D.tailAction (a r)) (fderiv ℝ a r w.1 + w.2) :=
    Proofs.M09.shiftedCost_fderiv D.prefixAction D.tailAction a (P r) r hL hS hra hp w
  refine ⟨?_, ?_⟩
  · simpa only [add_zero, fderiv_apply_one_eq_deriv, a] using hform (1, 0)
  · intro v
    simpa only [map_zero, zero_add, a] using hform (0, v)

end PoincareConjecture.M14.GaugeEndpointFamily
