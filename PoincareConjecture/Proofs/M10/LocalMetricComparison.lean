import PoincareConjecture.Proofs.M10.PullbackMetric
import PoincareConjecture.Proofs.M10.NormalizedDifferential
import PoincareConjecture.Proofs.M10.NormedSegmentDistance
import PoincareConjecture.Proofs.M10.VectorDistance









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option backward.isDefEq.respectTransparency false in

theorem local_normalized_metric_comparison (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Y)
    (hL : ∀ v, ‖L v‖ = g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v))
    {r : ℝ≥0} (hr : (1 : ℝ) < r) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧
      LipschitzOnWith r (e ∘ L.symm) (L '' V) ∧
      LipschitzOnWith r (L ∘ e.symm) (e '' V) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hsharp := eventually_pullback_tangentNorm_comparison g
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (heD.mfderiv_bijective hx) hr
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_source.mem_nhds hx) hsharp)
  have hWsource : W ⊆ e.source := fun y hy ↦ (hWsub hy).1
  have hWbound : ∀ y ∈ W, ∀ v,
      ‖L v‖ / (r : ℝ) ≤ g.tangentNorm (e y) (mfderiv (𝓡 n) (𝓡 n) e y v) ∧
      g.tangentNorm (e y) (mfderiv (𝓡 n) (𝓡 n) e y v) ≤ r * ‖L v‖ := by
    intro y hy v
    simpa only [hL] using (hWsub hy).2 v
  have heWopen : IsOpen (e '' W) := e.isOpen_image_of_subset_source hWopen hWsource
  have heWtarget : e '' W ⊆ e.target := image_mono hWsource |>.trans e.image_source_subset
  obtain ⟨ε, hε, hεsub⟩ := EMetric.mem_nhds_iff.mp
    (heWopen.mem_nhds (mem_image_of_mem e hxW))
  obtain ⟨a, ha, haε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (3 : ℝ≥0∞)) (by norm_num) hε.ne'
  have haε' : (a : ℝ≥0∞) + a + a < ε := by
    convert haε using 1
    ring
  have hball : ∀ q, g.edist (e x) q < (a : ℝ≥0∞) + a + a → q ∈ e '' W := by
    intro q hq
    apply hεsub
    change edist q (e x) < ε
    rw [edist_comm]
    exact hq.trans haε'
  obtain ⟨b, hb, hbsub⟩ := Metric.mem_nhds_iff.mp
    ((L.toHomeomorph.isOpenMap W hWopen).mem_nhds (mem_image_of_mem L hxW))
  change Metric.ball (L x) b ⊆ L '' W at hbsub
  have hBinW : MapsTo L.symm (Metric.ball (L x) b) W := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hbsub hy
    simpa only [L.symm_apply_apply] using hz
  have hforward : LipschitzOnWith r (e ∘ L.symm) (Metric.ball (L x) b) := by
    intro y hy z hz
    apply riemannianEDist_le_of_normed_differential_bound g
      (convex_ball _ _) Metric.isOpen_ball
      (he.comp L.symm.toContinuousLinearMap.contMDiff.contMDiffOn
        (fun w hw ↦ hWsource (hBinW hw))) ?_ hy hz
    intro w hw v
    exact normalized_forward_differential_bound g L
      (heD.mdifferentiableAt (hWsource (hBinW hw)))
      (fun u ↦ (hWbound _ (hBinW hw) u).2) v
  have hinvcont : ContinuousOn (L ∘ e.symm) (e '' W) :=
    L.continuous.comp_continuousOn (e.symm.continuousOn.mono heWtarget)
  have hinvdiff : ∀ q ∈ e '' W,
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, Y) (L ∘ e.symm) q := fun q hq ↦
    L.differentiableAt.mdifferentiableAt.comp q
      (heD.mdifferentiableAt_symm (heWtarget hq))
  have hinvbound : ∀ q ∈ e '' W, ∀ v : TangentSpace (𝓡 n) q,
      ‖mvfderiv (𝓡 n) (L ∘ e.symm) q v‖ ≤ r * g.tangentNorm q v := by
    intro q hq v
    have hqW : e.symm q ∈ W := by
      obtain ⟨y, hy, rfl⟩ := hq
      simpa only [e.left_inv (hWsource hy)] using hy
    exact normalized_inverse_differential_bound g L e heD (heWtarget hq)
      (zero_lt_one.trans hr) (fun u ↦ (hWbound _ hqW u).1) v
  let V := (W ∩ L ⁻¹' Metric.ball (L x) b) ∩
    (e.source ∩ e ⁻¹' Metric.eball (e x) (a : ℝ≥0∞))
  have hVopen : IsOpen V :=
    (hWopen.inter (Metric.isOpen_ball.preimage L.continuous)).inter
      (e.isOpen_inter_preimage Metric.isOpen_eball)
  have hxV : x ∈ V := by
    refine ⟨⟨hxW, Metric.mem_ball_self hb⟩, hx, ?_⟩
    exact Metric.mem_eball_self (by exact_mod_cast ha)
  refine ⟨V, hVopen, hxV, fun y hy ↦ hy.2.1, hforward.mono ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hz.1.2
  intro q hq q' hq'
  apply edist_le_mul_riemannianEDist_of_vector_differential g hinvcont hinvdiff
    hinvbound hball
  · obtain ⟨y, hy, rfl⟩ := hq
    change edist (e x) (e y) < (a : ℝ≥0∞)
    simpa only [edist_comm] using
      (show edist (e y) (e x) < (a : ℝ≥0∞) from hy.2.2)
  · obtain ⟨y, hy, rfl⟩ := hq'
    change edist (e x) (e y) < (a : ℝ≥0∞)
    simpa only [edist_comm] using
      (show edist (e y) (e x) < (a : ℝ≥0∞) from hy.2.2)

end PoincareConjecture.M10
