import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRescaling












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology

attribute [local instance] Classical.propDecidable

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60AreaDensity_congr_of_eventuallyEq (g : RiemannianMetric n M)
    {f h : LoopPlane → M} {z : LoopPlane} (hf : f =ᶠ[𝓝 z] h) :
    m60AreaDensity g f z = m60AreaDensity g h z := by
  have hi (u v : EuclideanSpace ℝ (Fin n)) : g.inner (f z) u v = g.inner (h z) u v :=
    congrArg (fun p : M => g.inner p u v) hf.eq_of_nhds
  simp only [m60AreaDensity, m60AreaGram, hf.mfderiv_eq, hi]
  rfl



theorem m60AreaDensity_piecewise_closedBall_ae (g : RiemannianMetric n M)
    (f h : LoopPlane → M) (r : ℝ) :
    m60AreaDensity g ((Metric.closedBall (0 : LoopPlane) r).piecewise f h) =ᵐ[volume]
      (Metric.closedBall (0 : LoopPlane) r).piecewise
        (m60AreaDensity g f) (m60AreaDensity g h) := by
  filter_upwards [compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0 : LoopPlane) r)]
    with z hz
  have hne : ‖z‖ ≠ r := by simpa only [mem_compl_iff, Metric.mem_sphere, dist_zero_right] using hz
  by_cases hi : z ∈ Metric.closedBall (0 : LoopPlane) r
  · have hb : z ∈ Metric.ball (0 : LoopPlane) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        lt_of_le_of_ne (by simpa only [Metric.mem_closedBall, dist_zero_right] using hi) hne
    have heq : (Metric.closedBall (0 : LoopPlane) r).piecewise f h =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_ball.mem_nhds hb] with x hx
      exact piecewise_eq_of_mem _ _ _ (Metric.ball_subset_closedBall hx)
    rw [piecewise_eq_of_mem _ _ _ hi]
    exact m60AreaDensity_congr_of_eventuallyEq g heq
  · have heq : (Metric.closedBall (0 : LoopPlane) r).piecewise f h =ᶠ[𝓝 z] h := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hi] with x hx
      exact piecewise_eq_of_notMem _ _ _ hx
    rw [piecewise_eq_of_notMem _ _ _ hi]
    exact m60AreaDensity_congr_of_eventuallyEq g heq




theorem m60AreaIntegral_piecewise_closedBall (g : RiemannianMetric n M)
    (f h : LoopPlane → M) (r : ℝ) (S : Set LoopPlane)
    (hf : IntegrableOn (m60AreaDensity g f) (Metric.closedBall 0 r ∩ S) volume)
    (hh : IntegrableOn (m60AreaDensity g h) ((Metric.closedBall 0 r)ᶜ ∩ S) volume) :
    IntegrableOn (m60AreaDensity g ((Metric.closedBall (0 : LoopPlane) r).piecewise f h))
      S volume ∧
      (∫ z in S, m60AreaDensity g ((Metric.closedBall (0 : LoopPlane) r).piecewise f h) z) =
        (∫ z in Metric.closedBall (0 : LoopPlane) r ∩ S, m60AreaDensity g f z) +
          ∫ z in (Metric.closedBall (0 : LoopPlane) r)ᶜ ∩ S, m60AreaDensity g h z := by
  have hfi : IntegrableOn (m60AreaDensity g f) (Metric.closedBall 0 r) (volume.restrict S) := by
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_closedBall] using hf
  have hhi : IntegrableOn (m60AreaDensity g h) (Metric.closedBall 0 r)ᶜ (volume.restrict S) := by
    simpa only [IntegrableOn, Measure.restrict_restrict measurableSet_closedBall.compl] using hh
  have heq := (m60AreaDensity_piecewise_closedBall_ae g f h r).filter_mono
    (ae_mono (Measure.restrict_le_self (s := S)))
  refine ⟨(Integrable.piecewise measurableSet_closedBall hfi hhi).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_piecewise measurableSet_closedBall hfi hhi,
    Measure.restrict_restrict measurableSet_closedBall,
    Measure.restrict_restrict measurableSet_closedBall.compl]

end PoincareConjecture
