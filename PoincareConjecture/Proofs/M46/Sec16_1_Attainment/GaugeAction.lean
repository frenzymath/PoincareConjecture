import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeActionLimit
import PoincareConjecture.Proofs.M08.PathGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T tau : ℝ} {x y : G.Point}

theorem backward_square_density_integrable (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (p : M14BackwardPath G T 0 tau x y) :
    IntervalIntegrable (fun s => M14.pathSquarePotential p s +
      (1 / 2 : ℝ) * M14.pathSquareKinetic p s) volume 0 (Real.sqrt tau) := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hp : ContinuousOn (M14.pathSquarePotential p) (M14SqrtParameterInterval 0 tau) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (H.scalar_smooth.continuous.comp_continuousOn (M14.squarePath_continuousOn p))
  have hk : IntervalIntegrable (M14.pathSquareKinetic p) volume
      (Real.sqrt 0) (Real.sqrt tau) := M14.squarePath_kinetic_intervalIntegrable p hM12
  have h := (hp.intervalIntegrable_of_Icc (Real.sqrt_le_sqrt p.tau_lt.le)).add
    (hk.const_mul (1 / 2 : ℝ))
  simpa only [Real.sqrt_zero] using h

theorem gauge_piece_action_eq (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (e : AttainmentGauge G) (p : M14BackwardPath G T 0 tau x y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.sqrt tau) (hab : a ≤ b)
    (hsrc : ∀ s ∈ Icc a b, p.curve (s ^ 2) ∈ e.source)
    (v : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b)
    (hv : (v : ℝ → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume.restrict (Icc a b)]
      deriv (fun s => (e.lift (p.curve (s ^ 2))).2.val)) :
    gaugePieceAction e (fun s => p.curve (s ^ 2)) v =
      ∫ s in a..b, M14.pathSquarePotential p s + (1 / 2 : ℝ) * M14.pathSquareKinetic p s := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hsub : Icc a b ⊆ M14SqrtParameterInterval 0 tau := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Icc_subset_Icc ha hb
  have hp : ContinuousOn (M14.pathSquarePotential p) (Icc a b) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (H.scalar_smooth.continuous.comp_continuousOn ((M14.squarePath_continuousOn p).mono hsub))
  have hpint : IntervalIntegrable (M14.pathSquarePotential p) volume a b :=
    hp.intervalIntegrable_of_Icc hab
  have hint := (backward_square_density_integrable hM12 p).mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le (Real.sqrt_nonneg tau)]
    exact Icc_subset_Icc ha hb)
  have hkin : (∫ s in a..b, (1 / 2 : ℝ) *
      gaugeLiftMetric e.index e.lift e.center (p.curve (s ^ 2)) (v s) (v s)) =
      ∫ s in a..b, (M14.pathSquarePotential p s +
        (1 / 2 : ℝ) * M14.pathSquareKinetic p s) - M14.pathSquarePotential p s := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    have hmem : ∀ᵐ s ∂volume.restrict (Icc a b), s ∈ Ioo a b := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hv, hmem] with s hs hsI
    rw [hs, squarePath_gaugeLiftMetric_eq e.index e.lift e.center p e.smooth
      e.right_inv ha hb hsI hsrc]
    ring
  unfold gaugePieceAction
  rw [hkin, intervalIntegral.integral_sub hint hpint]
  change (_ - ∫ s in a..b, M14.pathSquarePotential p s) +
    (∫ s in a..b, M14.pathSquarePotential p s) = _
  exact sub_add_cancel _ _

theorem gauge_partition_action_eq (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (p : M14BackwardPath G T 0 tau x y) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (ht : Monotone t) (hzero : t 0 = 0) (hlast : t (Fin.last m) = Real.sqrt tau)
    (e : Fin m → AttainmentGauge G)
    (hsrc : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) → p.curve (s ^ 2) ∈ (e i).source)
    (v : ∀ i : Fin m, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (t i.castSucc) (t i.succ))
    (hv : ∀ i, (v i : ℝ → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
        deriv (fun s => ((e i).lift (p.curve (s ^ 2))).2.val)) :
    (∑ i, gaugePieceAction (e i) (fun s => p.curve (s ^ 2)) (v i)) = M14BackwardLAction G p := by
  have ha (i : Fin m) : 0 ≤ t i.castSucc := hzero ▸ ht (Fin.zero_le _)
  have hb (i : Fin m) : t i.succ ≤ Real.sqrt tau := hlast ▸ ht (Fin.le_last _)
  have hab (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hint := backward_square_density_integrable hM12 p
  have hpieces (i : Fin m) : IntervalIntegrable (fun s => M14.pathSquarePotential p s +
      (1 / 2 : ℝ) * M14.pathSquareKinetic p s) volume (t i.castSucc) (t i.succ) :=
    hint.mono_set (by
      rw [uIcc_of_le (hab i), uIcc_of_le (Real.sqrt_nonneg tau)]
      exact Icc_subset_Icc (ha i) (hb i))
  calc
    _ = ∑ i : Fin m, ∫ s in t i.castSucc..t i.succ,
        M14.pathSquarePotential p s + (1 / 2 : ℝ) * M14.pathSquareKinetic p s :=
      Finset.sum_congr rfl (fun i _ =>
        gauge_piece_action_eq hM12 (e i) p (ha i) (hb i) (hab i) (hsrc i) (v i) (hv i))
    _ = ∫ s in t 0..t (Fin.last m),
        M14.pathSquarePotential p s + (1 / 2 : ℝ) * M14.pathSquareKinetic p s :=
      (M08.integrable_sum_fin_partition t _ hpieces).2
    _ = _ := by
      rw [hzero, hlast]
      simpa only [Real.sqrt_zero] using (M14.backwardPath_squareAction_eq p).symm

end PoincareConjecture.Proofs.M46
