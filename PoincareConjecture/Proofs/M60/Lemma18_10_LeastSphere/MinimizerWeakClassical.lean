import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerClassicalGradient
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerNearLaplacianHolder









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)



theorem suWeakPartial_congr_ae {O : Set Plane} {i : Fin 2}
    {u v p q : Plane → ℝ} (hw : HasWeakPartialDeriv i p u O)
    (hu : v =ᵐ[volume.restrict O] u) (hp : q =ᵐ[volume.restrict O] p) :
    HasWeakPartialDeriv i q v O := by
  intro φ hφ hc hs
  calc
    _ = ∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      integral_congr_ae (hu.mono fun x hx => by rw [hx])
    _ = -(∫ x in O, p x * φ x) := hw φ hφ hc hs
    _ = _ := congrArg Neg.neg (integral_congr_ae (hp.mono fun x hx => by rw [hx]))



theorem suPlaneColumns_continuousOn {m : ℕ} {O : Set Plane}
    {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
    (hp : ∀ i, ContinuousOn (p i) O) :
    ContinuousOn (fun x => suPlaneColumns (fun i => p i x)) O := by
  have h (i : Fin 2) :=
    (ContinuousLinearMap.smulRightL ℝ Plane (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.comp_continuousOn (hp i)
  apply ((h 0).add (h 1)).congr
  intro x _
  ext v
  simp [suPlaneColumns]





theorem suNearLaplacian_C1_holder :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (m : ℕ)
      {u : Plane → EuclideanSpace ℝ (Fin m)}
      {p : Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
      {H : Fin 2 → Fin 2 → Plane → EuclideanSpace ℝ (Fin m)}
      {f : Plane → EuclideanSpace ℝ (Fin m)},
      MemLp u 2 (volume.restrict (Metric.ball 0 2)) →
      (∀ i, MemLp (p i) 2 (volume.restrict (Metric.ball 0 2))) →
      (∀ i b, HasWeakPartialDeriv i (fun x => p i x b) (fun x => u x b)
        (Metric.ball 0 2)) →
      (∀ i j, MemLp (H i j) 2 (volume.restrict (Metric.ball 0 2))) →
      (∀ i j b, HasWeakPartialDeriv j (fun x => H i j x b) (fun x => p i x b)
        (Metric.ball 0 2)) →
      MemLp f 4 (volume.restrict (Metric.ball 0 2)) →
      ContinuousOn u (Metric.ball 0 2) →
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 2),
        ‖(∑ i : Fin 2, H i i x) - f x‖ ≤
          δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2)) →
      ContDiffOn ℝ 1 u (Metric.ball 0 (1 / 4)) ∧
      (∀ i : Fin 2, ∀ᵐ x ∂volume.restrict (Metric.ball 0 (1 / 4)),
        fderiv ℝ u x (EuclideanSpace.single i 1) = p i x) ∧
      ∀ x ∈ Metric.closedBall (0 : Plane) (1 / 8),
        ∀ y ∈ Metric.closedBall (0 : Plane) (1 / 8),
        dist (fderiv ℝ u x) (fderiv ℝ u y) ≤
          C * Real.sqrt (suHessianEnergy H (Metric.ball 0 2) +
            Real.sqrt (∫ z in Metric.ball 0 2, ‖f z‖ ^ 4)) *
              Real.sqrt (Real.sqrt (dist x y)) := by
  obtain ⟨δ, C, hδ, hC, hholder⟩ := suNearLaplacian_weak_gradient_holder
  refine ⟨δ, 2 * C, hδ, by positivity, ?_⟩
  intro m u p H f hu hp hw hH hwH hf huc hres
  obtain ⟨P, hPc, hPae, hPb⟩ := hholder m hu hp hw hH hwH hf hres
  have hhalf : Metric.ball (0 : Plane) (1 / 2) ⊆ Metric.ball 0 2 :=
    Metric.ball_subset_ball (by norm_num)
  have hquarter : Metric.ball (0 : Plane) (1 / 4) ⊆ Metric.ball 0 (1 / 2) :=
    Metric.ball_subset_ball (by norm_num)
  have hLP (i : Fin 2) : MemLp (P i) 2 (volume.restrict (Metric.ball 0 (1 / 2))) :=
    (memLp_congr_ae (hPae i)).mpr ((hp i).mono_measure (Measure.restrict_mono hhalf le_rfl))
  have hwP (i : Fin 2) (b : Fin m) :
      HasWeakPartialDeriv i (fun x => P i x b) (fun x => u x b)
        (Metric.ball 0 (1 / 2)) :=
    suWeakPartial_congr_ae ((hw i b).restrict Metric.isOpen_ball hhalf)
      Filter.EventuallyEq.rfl ((hPae i).mono fun x hx => congrArg (fun v => v b) hx)
  have hd (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) (1 / 4)) :
      HasFDerivAt u (suPlaneColumns (fun i => P i x)) x :=
    suContinuous_weak_gradient_hasFDerivAt_on_ball (by norm_num)
      (hu.mono_measure (Measure.restrict_mono hhalf le_rfl)) hLP hwP
      (huc.mono hhalf) (fun i => (hPc i).mono Metric.ball_subset_closedBall) x
      (by norm_num at hx ⊢; exact hx)
  have hdc : ContinuousOn (fderiv ℝ u) (Metric.ball (0 : Plane) (1 / 4)) :=
    (suPlaneColumns_continuousOn (fun i =>
      (hPc i).mono (hquarter.trans Metric.ball_subset_closedBall))).congr
        (fun x hx => (hd x hx).fderiv)
  have hcol (i : Fin 2) (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) (1 / 4)) :
      fderiv ℝ u x (EuclideanSpace.single i 1) = P i x := by
    rw [(hd x hx).fderiv]
    fin_cases i <;> simp [suPlaneColumns]
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    exact ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
      by simp, contDiffOn_zero.mpr hdc⟩
  · intro i
    filter_upwards [(hPae i).filter_mono
      (ae_mono (Measure.restrict_mono hquarter le_rfl)),
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxO
    exact (hcol i x hxO).trans hx
  · intro x hx y hy
    have hxq : x ∈ Metric.ball (0 : Plane) (1 / 4) :=
      Metric.closedBall_subset_ball (by norm_num) hx
    have hyq : y ∈ Metric.ball (0 : Plane) (1 / 4) :=
      Metric.closedBall_subset_ball (by norm_num) hy
    have hb (i : Fin 2) := hPb i x (Metric.closedBall_subset_closedBall (by norm_num) hx)
      y (Metric.closedBall_subset_closedBall (by norm_num) hy)
    have h := suPlaneOperator_norm_le (fderiv ℝ u x - fderiv ℝ u y)
      (C := C * Real.sqrt (suHessianEnergy H (Metric.ball 0 2) +
        Real.sqrt (∫ z in Metric.ball 0 2, ‖f z‖ ^ 4)) * Real.sqrt (Real.sqrt (dist x y)))
      (by positivity) (fun i => by
        simpa only [sub_apply, hcol i x hxq, hcol i y hyq, dist_eq_norm] using hb i)
    simpa only [dist_eq_norm, mul_assoc] using h

end PoincareConjecture.M60

end
