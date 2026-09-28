import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.AnnularLengthMap
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ScalarFactorArea
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere

set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

universe u

namespace PoincareConjecture

theorem m60AnnularLengthMap_area_zero
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {beta : ℝ → M} {a b : ℝ → ℝ}
    {A B C : ℝ≥0} (ha : LipschitzWith A a) (hb : LipschitzWith B b)
    {S : Set ℝ} (hS : Convex ℝ S) (haS : ∀ t, a t ∈ S) (hbS : ∀ t, b t ∈ S)
    (hbeta : ∀ s ∈ S, ∀ t ∈ S,
      g.edist (beta s) (beta t) ≤ C * ENNReal.ofReal |s - t|)
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, Function.Periodic
      (fun t => beta (M60.lengthParameterInterpolation a b (u, t))) rampPeriod) :
    IntegrableOn (m60AreaDensity g (m60AnnularLengthMap beta a b))
      ((closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet) volume ∧
      (∫ z in (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet,
        m60AreaDensity g (m60AnnularLengthMap beta a b) z) = 0 := by
  let Q := (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ ball (0 : LoopPlane) 1
  have hQ : IsOpen Q := isClosed_closedBall.isOpen_compl.inter isOpen_ball
  have hnorm (z : LoopPlane) (hz : z ∈ Q) : 1 / 2 < ‖z‖ ∧ ‖z‖ < 1 := by
    simpa only [Q, mem_inter_iff, mem_compl_iff, mem_closedBall, mem_ball,
      dist_zero_right, not_le] using hz
  obtain ⟨_, hi, hzero⟩ := m60AreaIntegral_eq_zero_of_locally_scalar_increment_bound
    g (F := m60AnnularLengthMap beta a b) hQ.measurableSet (by
      intro z hz
      have hn : z ≠ 0 := by
        intro heq
        have h := (hnorm z hz).1
        rw [heq, norm_zero] at h
        norm_num at h
      obtain ⟨theta, K, U, hU, hLip, heq⟩ := m60AnnularLengthMap_local_scalar ha hb hp hn
      obtain ⟨V, hVU, hV, hzV⟩ := _root_.mem_nhds_iff.mp (inter_mem hU (hQ.mem_nhds hz))
      let ell : LoopPlane → ℝ := fun w =>
        M60.lengthParameterInterpolation a b (2 * ‖w‖ - 1, theta w)
      have hmem (w : LoopPlane) (hw : w ∈ V) : ell w ∈ S :=
        M60.lengthParameterInterpolation_mem hS haS hbS
          ⟨by linarith [(hnorm w (hVU hw).2).1], by linarith [(hnorm w (hVU hw).2).2]⟩
      refine ⟨ell, V, K, C, hV, hzV, hLip.mono (fun w hw => (hVU hw).1), ?_⟩
      intro x hx y hy
      rw [heq x ⟨(hnorm x (hVU hx).2).1.le, (hnorm x (hVU hx).2).2.le⟩,
        heq y ⟨(hnorm y (hVU hy).2).1.le, (hnorm y (hVU hy).2).2.le⟩]
      exact hbeta _ (hmem x hx) _ (hmem y hy))
  have heq : Q =ᵐ[volume]
      ((closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet : Set LoopPlane) := by
    filter_upwards [M60.haar_ball_ae_eq_closedBall volume (0 : LoopPlane) 1] with z hz
    exact congrArg (fun b : Prop => z ∈ (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∧ b) hz
  refine ⟨(integrableOn_congr_set_ae heq).mp hi, ?_⟩
  rwa [← setIntegral_congr_set heq]

end PoincareConjecture
