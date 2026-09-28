import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzArea
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere









set_option autoImplicit false

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]




theorem m60AreaIntegral_bound_on_closedBall (g : RiemannianMetric n M)
    {f : LoopPlane → M} (p : LoopPlane) (R : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ closedBall p R, ∀ y ∈ closedBall p R,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖) :
    IntegrableOn (m60AreaDensity g f) (closedBall p R) volume ∧
      (∫ z in closedBall p R, m60AreaDensity g f z) ≤
        (2 * L) ^ 2 * volume.real (closedBall p R) := by
  obtain ⟨hi, hb⟩ := m60AreaIntegral_bound_of_metric_lipschitzOn g isOpen_ball
    measure_ball_lt_top.ne hL (fun x hx y hy =>
      hf x (ball_subset_closedBall hx) y (ball_subset_closedBall hy))
  have heq := M60.haar_ball_ae_eq_closedBall volume p R
  refine ⟨(integrableOn_congr_set_ae heq).mp hi, ?_⟩
  rwa [← setIntegral_congr_set heq, ← measureReal_congr heq]



theorem m60AreaDensity_integrableOn_of_disk_lipschitz (g : RiemannianMetric n M)
    {f : LoopPlane → M} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y : LoopDisk,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :
    IntegrableOn (m60AreaDensity g f) loopDiskSet volume :=
  (m60AreaIntegral_bound_on_closedBall g 0 1 hL
    (fun x hx y hy => hf ⟨x, hx⟩ ⟨y, hy⟩)).1




theorem m60AreaIntegral_bound_on_annulus (g : RiemannianMetric n M)
    {f : LoopPlane → M} (r : ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
      ∀ y ∈ loopDiskSet ∩ {z | r ≤ ‖z‖},
        g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖) :
    IntegrableOn (m60AreaDensity g f) ((closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet) volume ∧
      (∫ z in (closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet, m60AreaDensity g f z) ≤
        (2 * L) ^ 2 * volume.real ((closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet) := by
  let U := (closedBall (0 : LoopPlane) r)ᶜ ∩ ball (0 : LoopPlane) 1
  have hU : IsOpen U := isClosed_closedBall.isOpen_compl.inter isOpen_ball
  have hsub : U ⊆ loopDiskSet ∩ {z | r ≤ ‖z‖} := by
    intro x hx
    refine ⟨ball_subset_closedBall hx.2, ?_⟩
    have h := hx.1
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at h
    exact h.le
  have hfinite : volume U ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)
  obtain ⟨hi, hb⟩ := m60AreaIntegral_bound_of_metric_lipschitzOn g hU hfinite hL
    (fun x hx y hy => hf x (hsub hx) y (hsub hy))
  have heq : U =ᵐ[volume] ((closedBall (0 : LoopPlane) r)ᶜ ∩ loopDiskSet : Set LoopPlane) := by
    filter_upwards [M60.haar_ball_ae_eq_closedBall volume (0 : LoopPlane) 1] with z hz
    exact congrArg (fun b : Prop => z ∈ (closedBall (0 : LoopPlane) r)ᶜ ∧ b) hz
  refine ⟨(integrableOn_congr_set_ae heq).mp hi, ?_⟩
  rwa [← setIntegral_congr_set heq, ← measureReal_congr heq]

end PoincareConjecture
