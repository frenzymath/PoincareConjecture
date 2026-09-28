import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem metric_lipschitz_nhds_of_contMDiffAt
    (g : RiemannianMetric n M) {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) 1 f x) :
    ∃ C : ℝ≥0, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        g.edist (f y) (f z) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  let e := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  have he : e.MDifferentiable (𝓡 n) (𝓡 n) := mdifferentiable_chart _
  have hx : f x ∈ e.source := mem_chart_source _ _
  let chi := M40.normalizedSmoothChart e he hx
  have hchi : f x ∈ chi.source := by
    simpa only [chi, M40.normalizedSmoothChart_source] using hx
  obtain ⟨R, hR, -, hInv, -⟩ := M40.normalizedSmoothChart_exists_lipschitz_ball
    e he hx contMDiffOn_chart contMDiffOn_chart_symm 2 (by norm_num)
  have hcoord : ContDiffAt ℝ 1 (chi ∘ f) x :=
    (((M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart).contMDiffAt
      (chi.open_source.mem_nhds hchi)).of_le (m := 1) (by norm_num)).comp x hf
      |>.contDiffAt
  obtain ⟨C, U, hU, hLip⟩ := hcoord.exists_lipschitzOnWith
  have hwindow : U ∩ f ⁻¹' chi.source ∩
      (chi ∘ f) ⁻¹' Metric.ball (chi (f x)) R ∈ 𝓝 x :=
    inter_mem (inter_mem hU (hf.continuousAt.preimage_mem_nhds
      (chi.open_source.mem_nhds hchi)))
      (hcoord.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hR))
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hwindow
  have hLipV : LipschitzOnWith C (chi ∘ f) V := hLip.mono (fun y hy => (hVsub hy).1.1)
  have hcomp := hInv.comp hLipV (fun y hy => (hVsub hy).2)
  refine ⟨2 * C, V, hV, hxV, ?_⟩
  intro y hy z hz
  have hh := hcomp hy hz
  change g.edist (chi.symm (chi (f y))) (chi.symm (chi (f z))) ≤
    ((2 * C : ℝ≥0) : ℝ≥0∞) * edist y z at hh
  simpa only [chi.left_inv (hVsub hy).1.2, chi.left_inv (hVsub hz).1.2,
    edist_dist, dist_eq_norm] using hh

theorem compact_metric_control_near_diagonal
    (g : RiemannianMetric n M) {rho : E → M} {K O : Set E}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hrho : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) 1 rho O) :
    ∃ C : ℝ, 0 < C ∧ ∃ V : Set (E × E), IsOpen V ∧
      (∀ z ∈ K, (z, z) ∈ V) ∧
      ∀ p ∈ V, g.edist (rho p.1) (rho p.2) ≤ ENNReal.ofReal (C * ‖p.1 - p.2‖) := by
  classical
  have hlocal (z : K) := metric_lipschitz_nhds_of_contMDiffAt g
    (hrho.contMDiffAt (hO.mem_nhds (hKO z.property)))
  choose C U hU hmem hLip using hlocal
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' (fun z hz => U ⟨z, hz⟩)
    (fun z hz => (hU ⟨z, hz⟩).mem_nhds (hmem ⟨z, hz⟩))
  let L : ℝ := (∑ z ∈ s, (C z : ℝ)) + 1
  let V : Set (E × E) := ⋃ z ∈ s, U z ×ˢ U z
  have hL : 0 < L := by
    have hsnonneg := Finset.sum_nonneg (fun z (_ : z ∈ s) => (C z).coe_nonneg)
    dsimp only [L]
    linarith
  refine ⟨L, hL, V, isOpen_biUnion (fun z _ => (hU z).prod (hU z)), ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
    exact mem_iUnion₂.mpr ⟨w, hw, hzw, hzw⟩
  · intro p hp
    obtain ⟨z, hz, hp0, hp1⟩ := mem_iUnion₂.mp hp
    have hC : (C z : ℝ) ≤ L := by
      have hsum := Finset.single_le_sum (fun y (_ : y ∈ s) => (C y).coe_nonneg) hz
      dsimp only [L]
      linarith
    have hh := hLip z p.1 hp0 p.2 hp1
    calc
      _ ≤ (C z : ℝ≥0∞) * ENNReal.ofReal ‖p.1 - p.2‖ := hh
      _ = ENNReal.ofReal ((C z : ℝ) * ‖p.1 - p.2‖) := by
        rw [ENNReal.ofReal_mul (C z).coe_nonneg, ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal (L * ‖p.1 - p.2‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

end PoincareConjecture.M64
