import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.LowerCurvature










noncomputable section
set_option autoImplicit false

open Set Filter Topology
open Poincare.GromovHausdorff

namespace Poincare.Alexandrov


theorem curvatureGEnegOne_of_pointedGHConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace} {Y : FiniteDiameterBasedMetricSpace}
    (hX : ∀ j, CurvatureGEnegOne (X j).carrier) (h : PointedGHConverges X Y) :
    CurvatureGEnegOne Y.carrier := by
  obtain ⟨f, hf⟩ := exists_approximating_maps_of_pointedGHConverges h
  intro q hq
  exact fourPoint_comparison_of_tendsto_dist hX hq (fun a b => hf (q a) (q b))



theorem curvatureGEnegOne_of_pointedGHConvergesUnbounded
    {X : ℕ → BasedMetricSpaceBundle} {Y : BasedMetricSpaceBundle}
    (hX : ∀ j, CurvatureGEnegOne (X j).carrier)
    (h : PointedGHConvergesUnbounded X Y) :
    CurvatureGEnegOne Y.carrier := by
  intro q hq
  let r : ℝ := 1 + ∑ i : Fin 4, dist (q i) Y.base
  have hsum : 0 ≤ ∑ i : Fin 4, dist (q i) Y.base :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hr : 0 < r := by dsimp [r]; linarith
  have hqr (i : Fin 4) : q i ∈ Metric.ball Y.base r := by
    rw [Metric.mem_ball]
    have hi := Finset.single_le_sum (fun (j : Fin 4) _ =>
      show 0 ≤ dist (q j) Y.base from dist_nonneg) (Finset.mem_univ i)
    dsimp [r]
    linarith
  obtain ⟨δ, _, hpos, hconv⟩ := h r hr
  have hballs (j : ℕ) : CurvatureGEnegOne (ballModel (X j) (r + δ j) (hpos j)).carrier :=
    (hX j).of_isometry (f := Subtype.val) (Isometry.of_dist_eq (fun _ _ => rfl))
  have hlimit := curvatureGEnegOne_of_pointedGHConverges hballs hconv
  let q' : Fin 4 → (ballModel Y r hr).carrier := fun i => ⟨q i, hqr i⟩
  have hq' : Function.Injective q' := fun a b hab => hq (congrArg Subtype.val hab)
  exact hlimit q' hq'

end Poincare.Alexandrov
