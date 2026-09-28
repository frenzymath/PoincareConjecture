import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m60Curve_edist_le_of_speed_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : ℝ → M} (hf : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 f)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ t, g.tangentNorm (f t) (curveVelocity f t) ≤ L)
    (s t : ℝ) : g.edist (f s) (f t) ≤ ENNReal.ofReal L * ENNReal.ofReal |s - t| := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hordered (a b : ℝ) (hab : a ≤ b) :
      g.edist (f a) (f b) ≤ ENNReal.ofReal L * ENNReal.ofReal |a - b| := by
    have hi := intervalIntegral.integral_mono (μ := volume) hab
      ((M04.continuous_pathSpeed g hf).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b) hbound
    have hi' : (∫ t in a..b, M04.pathSpeed g f t) ≤ (b - a) * L := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
    calc
      g.edist (f a) (f b) ≤ g.pathELength f a b :=
        Manifold.riemannianEDist_le_pathELength hf.contMDiffOn rfl rfl hab
      _ = ENNReal.ofReal (∫ t in a..b, M04.pathSpeed g f t) :=
        M04.pathELength_eq_ofReal_integral_pathSpeed g hf hab
      _ ≤ ENNReal.ofReal ((b - a) * L) := ENNReal.ofReal_le_ofReal hi'
      _ = ENNReal.ofReal L * ENNReal.ofReal |a - b| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm (b - a),
          ENNReal.ofReal_mul hL]
  rcases le_total s t with hst | hts
  · exact hordered s t hst
  · have heq : g.edist (f s) (f t) = g.edist (f t) (f s) :=
      Manifold.riemannianEDist_comm
    rw [heq, abs_sub_comm]
    exact hordered t s hts

theorem m60_exists_periodicLoop_lipschitz_bound
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (gamma : C1FreeLoopSpace (M := M)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t : ℝ,
      g.edist (periodicFreeLoop gamma s) (periodicFreeLoop gamma t) ≤
        ENNReal.ofReal L * ENNReal.ofReal |s - t| := by
  have hp : rampPeriod ≠ 0 := by dsimp [rampPeriod]; positivity
  obtain ⟨B, hB⟩ := ((Proofs.M58.periodic_freeLoopSpeed g gamma).compact_of_continuous hp
    (Proofs.M58.continuous_freeLoopSpeed g gamma)).bddAbove
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  apply m60Curve_edist_le_of_speed_bound g (Proofs.M58.contMDiff_periodicFreeLoop gamma)
    (le_max_right _ _)
  intro t
  exact (hB (mem_range_self t)).trans (le_max_left _ _)

theorem m60AngularPoint_lipschitz : LipschitzWith 1 Proofs.M58.angularPoint := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (Proofs.M58.hasDerivAt_angularPoint t).differentiableAt)
  intro t
  rw [(Proofs.M58.hasDerivAt_angularPoint t).deriv]
  apply NNReal.coe_le_coe.mp
  change ‖Proofs.M58.angularVector t‖ ≤ 1
  simp [Proofs.M58.angularVector, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.sin_sq_add_cos_sq]

theorem m60Disk_angular_trace_bound
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {gamma : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma) (s t : ℝ) :
    g.edist (D.map (Proofs.M58.angularPoint s)) (D.map (Proofs.M58.angularPoint t)) ≤
      ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal |s - t| := by
  have hd (x : ℝ) : Proofs.M58.angularPoint x ∈ loopDiskSet := by
    simp [loopDiskSet, Metric.mem_closedBall, Proofs.M58.norm_angularPoint]
  have h := D.lipschitz_on_disk ⟨Proofs.M58.angularPoint s, hd s⟩
    ⟨Proofs.M58.angularPoint t, hd t⟩
  apply h.trans
  gcongr
  simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    m60AngularPoint_lipschitz.norm_sub_le s t

end PoincareConjecture
