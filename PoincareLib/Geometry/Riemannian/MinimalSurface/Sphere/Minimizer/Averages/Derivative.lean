import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Averages.Commutation

/-!
# Derivative bounds from local weak-gradient energy

The actual distributional columns are averaged on disks strictly inside
the original domain. Their square-root energy growth bounds the classical
derivative of each smooth average at the required scale. Source:
Sacks-Uhlenbeck Proposition 2.3 and Theorems 4.4-4.7; the weak-gradient
averaging derivation in `derivations/bubbling.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace PoincareMT.M60

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The translated normalized kernel has exactly the expected closed
disk support. Source: SU 2.3 and 4.4-4.7, admissible local averaging. -/
theorem suMollifier_translated_tsupport {r : ℝ} (hr : 0 < r) (x : Plane) :
    tsupport (fun y => mollifierEps hr (x - y)) = Metric.closedBall x r := by
  let T : Plane ≃ₜ Plane := (Homeomorph.neg Plane).trans (Homeomorph.addLeft x)
  have hfun : (fun y => mollifierEps hr (x - y)) = mollifierEps hr ∘ T := by
    ext y
    simp [T, sub_eq_add_neg]
  rw [hfun, tsupport_comp_eq_preimage, mollifierEps_tsupport_eq]
  ext y
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have hT : T y = x - y := by simp [T, sub_eq_add_neg]
  rw [hT, dist_eq_norm, norm_sub_rev]

/-- Genuine L2 data on a finite disk have a locally integrable zero
extension. This makes every displayed smooth average meaningful.
Source: SU 2.3 and 4.4-4.7, local weak mollification. -/
theorem suDisk_indicator_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    {u : Plane → E} {a : Plane} {r : ℝ}
    (hu : MemLp u 2 (volume.restrict (Metric.ball a r))) :
    LocallyIntegrable ((Metric.ball a r).indicator u) volume := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a r) < ⊤)⟩
  exact ((integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
    (hu.integrable (by norm_num))).locallyIntegrable

/-- The actual averaged weak gradient obeys the scale r to the negative
three-quarters. The estimate is independent of the target dimension.
Source: SU 2.3 and 4.4-4.7, the Holder representative argument. -/
theorem suMollifier_weak_gradient_bound {m : ℕ}
    {u : Plane → EuclideanSpace ℝ (Fin m)}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hu : MemLp u 2 (volume.restrict (Metric.ball 0 2)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun y => p i y b) (fun y => u y b)
      (Metric.ball 0 2)) {K : ℝ} (hK : 0 ≤ K)
    (henergy : ∀ i : Fin 2, ∀ a ∈ Metric.closedBall (0 : Plane) 1,
      ∀ r ∈ Ioc (0 : ℝ) 1,
        (∫ y in Metric.ball a r, ‖p i y‖ ^ 2) ≤ K * Real.sqrt r)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 16)
    (x : Plane) (hx : x ∈ Metric.closedBall (0 : Plane) (3 / 4)) :
    ‖fderiv ℝ (mollifierEps hr ⋆[lsmul ℝ ℝ, volume]
        (Metric.ball (0 : Plane) 2).indicator u) x‖ ≤
      (8 * Real.sqrt Real.pi * Real.sqrt K / Real.pi) *
        Real.sqrt (Real.sqrt r) / r := by
  have hsub : Metric.closedBall x r ⊆ Metric.ball (0 : Plane) 2 := by
    intro y hy
    have hy' := Metric.mem_closedBall.mp hy
    have hx' := Metric.mem_closedBall.mp hx
    exact Metric.mem_ball.mpr (by linarith [dist_triangle y x (0 : Plane)])
  have hx1 : x ∈ Metric.closedBall (0 : Plane) 1 :=
    Metric.closedBall_subset_closedBall (by norm_num) hx
  have huI := suDisk_indicator_locallyIntegrable hu
  have hpI (i : Fin 2) := suDisk_indicator_locallyIntegrable (hp i)
  have hcol (i : Fin 2) :
      ‖fderiv ℝ (mollifierEps hr ⋆[lsmul ℝ ℝ, volume]
          (Metric.ball (0 : Plane) 2).indicator u) x (EuclideanSpace.single i 1)‖ ≤
        (4 * Real.sqrt Real.pi * Real.sqrt K / Real.pi) *
          Real.sqrt (Real.sqrt r) / r := by
    rw [suWeak_convolution_fderiv Metric.isOpen_ball.measurableSet (hw i) huI (hpI i)
      (mollifierEps_smooth hr) (mollifierEps_compactSupport hr) x
      (by rw [suMollifier_translated_tsupport]; exact hsub)]
    have hpi := (hp i).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_closedBall.trans hsub) le_rfl)
    have hind : ∀ᵐ y ∂volume.restrict (Metric.ball x r),
        (Metric.ball (0 : Plane) 2).indicator (p i) y = p i y := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
      exact indicator_of_mem (hsub (Metric.ball_subset_closedBall hy)) (p i)
    have hint : (∫ y in Metric.ball x r,
        ‖(Metric.ball (0 : Plane) 2).indicator (p i) y‖) =
        ∫ y in Metric.ball x r, ‖p i y‖ :=
      integral_congr_ae (hind.mono fun y hy => congrArg norm hy)
    have hn := suMollifier_convolution_norm_le hr (hpI i) x
    rw [hint] at hn
    have he := henergy i x hx1 r ⟨hr, by linarith⟩
    calc
      _ ≤ 4 / (r ^ 2 * Real.pi) * ∫ y in Metric.ball x r, ‖p i y‖ := hn
      _ ≤ 4 / (r ^ 2 * Real.pi) *
          (Real.sqrt Real.pi * r * Real.sqrt (∫ y in Metric.ball x r, ‖p i y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (suL2_disk_L1_bound x hr hpi) (by positivity)
      _ ≤ 4 / (r ^ 2 * Real.pi) *
          (Real.sqrt Real.pi * r * Real.sqrt (K * Real.sqrt r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt he) (by positivity)) (by positivity)
      _ = _ := by
        rw [Real.sqrt_mul hK]
        field_simp
  have hb := suPlaneOperator_norm_le _ (by positivity) hcol
  exact hb.trans_eq (by ring)

end PoincareMT.M60

end
