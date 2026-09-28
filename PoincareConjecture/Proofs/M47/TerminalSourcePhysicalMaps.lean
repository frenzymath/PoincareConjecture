import PoincareConjecture.Proofs.M47.TerminalSourcePhysicalStage
import PoincareConjecture.Proofs.M47.TerminalSourceNormalAmbientCharts
import PoincareConjecture.Proofs.M47.TerminalSourceComponentCharts
import PoincareConjecture.Proofs.M47.TerminalSourceCountableScale










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace E N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T3Space M] [T3Space N]



theorem terminalSource_exists_physical_stage_maps
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (j : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : j.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (j x)
        (mfderiv (𝓡 3) (𝓡 3) j x v) (mfderiv (𝓡 3) (𝓡 3) j x w))
    (p0 : M) {A Rbig R rho : ℝ} {m : ℕ}
    (cover : TerminalSourceIndexedChartCover g p0 A R rho m)
    (hA : 0 < A) (hAR : A ≤ Rbig) (hRR : R ≤ Rbig)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R)
    (hcover : h.ball (j p0) (6 * Rbig) ⊆ j.target)
    (hbound : ∀ i, ∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients (cover.chart i).chart x v v ∧
        g.pullbackCoefficients (cover.chart i).chart x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) :
    let W := terminalSourceCountableDomain rho
    let C := Poincare.connectedComponentOpens E (j p0)
    let p : C := ⟨j p0, mem_connectedComponent⟩
    letI := terminalSourceComponentMetricSpace h (j p0)
    ∃ e : Fin (m + 1) → W → C,
      (∀ i x, (e i x).val = j ((cover.chart i).chart x.val)) ∧
      e 0 (terminalSourceCountableZero hrho) = p ∧
      (∀ i, Topology.IsOpenEmbedding (e i) ∧
        IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i)) ∧
      (∀ i x y, (1 / 2 : ℝ) * dist x y ≤ dist (e i x) (e i y) ∧
        dist (e i x) (e i y) ≤ (3 / 2 : ℝ) * dist x y) ∧
      (∀ i x, dist p (e i x) ≤ A + R) ∧
      (∀ i (x : W) (v w : TangentSpace (𝓡 3) x),
        (h.connectedComponentMetric (j p0)).inner (e i x)
          (mfderiv (𝓡 3) (𝓡 3) (e i) x v) (mfderiv (𝓡 3) (𝓡 3) (e i) x w) =
        g.inner ((cover.chart i).chart x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : W => (cover.chart i).chart y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : W => (cover.chart i).chart y.val) x w)) ∧
      ∃ core : Set W, IsCompact core ∧
        (∀ x : W, x ∈ core ↔ x.val ∈ Metric.closedBall (0 : E) (rho / 4)) ∧
        Metric.ball p A ⊆ ⋃ i, e i '' core := by
  let W := terminalSourceCountableDomain rho
  let C := Poincare.connectedComponentOpens E (j p0)
  let p : C := ⟨j p0, mem_connectedComponent⟩
  let : MetricSpace C := terminalSourceComponentMetricSpace h (j p0)
  let phi := fun (i : Fin (m + 1)) (x : W) => (cover.chart i).chart x.val
  let f := fun (i : Fin (m + 1)) (x : W) => j (phi i x)
  have hxSource (i : Fin (m + 1)) (x : W) : x.val ∈ (cover.chart i).chart.source := by
    rw [(cover.chart i).source]
    exact Metric.ball_subset_ball (by linarith : rho / 2 ≤ R) x.property
  have hphi (i : Fin (m + 1)) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (phi i) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) W x).comp (𝓡 3) M
      ((cover.chart i).chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hxSource i x))
  have hj : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ j := by
    intro x
    exact j.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource.symm ▸ mem_univ x)
  have hf (i : Fin (m + 1)) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (f i) := by
    intro x
    exact (hphi i x).comp (𝓡 3) N (hj (phi i x))
  have hfOpen (i : Fin (m + 1)) : Topology.IsOpenEmbedding (f i) := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hf i).contMDiff.continuous _ (hf i).isOpenMap
    intro x y hxy
    apply Subtype.ext
    exact (cover.chart i).chart.injOn (hxSource i x) (hxSource i y)
      (j.injOn (hsource.symm ▸ mem_univ _) (hsource.symm ▸ mem_univ _) hxy)
  have hball (i : Fin (m + 1)) (x : W) : f i x ∈ h.ball (j p0) (A + R) := by
    apply (terminalSourceNormal_ambient_chart_readouts g h j hsource hmetric p0
      (cover.chart i) hA hAR hRR hrho hrhoR (cover.centre_mem i) hcover).1
    exact Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) x.property)
  let e := fun i => terminalSourceComponentMap h (j p0) (f i) (hball i)
  refine ⟨e, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change j ((cover.chart 0).chart 0) = j p0
    rw [(cover.chart 0).zero, cover.centre_zero]
  · intro i
    exact terminalSourceComponentMap_geometry h (j p0) (f i) (hball i) (hfOpen i) (hf i)
  · intro i x y
    rw [(terminalSourceComponentMap_distances h (j p0) (f i) (hball i) x y).2]
    exact terminalSourceNormal_ambient_chart_distance_bounds g h j hsource hmetric p0
      (cover.chart i) hA hAR hRR hrho hrhoR (cover.centre_mem i) hcover
      (hbound i) x.property y.property
  · intro i x
    rw [(terminalSourceComponent_distances h (j p0) p (e i x)).2]
    exact (ENNReal.toReal_lt_of_lt_ofReal (hball i x)).le
  · intro i x v w
    rw [terminalSourceComponentMap_metric h (j p0) (f i) (hball i) (hf i)]
    have hchain := mfderiv_comp x (hj.mdifferentiable (by simp) (phi i x))
      ((hphi i).mdifferentiable (by simp) x)
    change mfderiv (𝓡 3) (𝓡 3) (f i) x =
      (mfderiv (𝓡 3) (𝓡 3) j (phi i x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (phi i) x) at hchain
    rw [hchain]
    exact (hmetric (phi i x) (mfderiv (𝓡 3) (𝓡 3) (phi i) x v)
      (mfderiv (𝓡 3) (𝓡 3) (phi i) x w)).symm
  · let core : Set W := (Subtype.val : W → E) ⁻¹' Metric.closedBall 0 (rho / 4)
    have hcoreBall : Metric.closedBall (0 : E) (rho / 4) ⊆ Metric.ball 0 (rho / 2) :=
      Metric.closedBall_subset_ball (by linarith)
    have hcompact : IsCompact core :=
      W.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage'
        (isCompact_closedBall (0 : E) (rho / 4))
        (fun z hz => ⟨⟨z, hcoreBall hz⟩, rfl⟩)
    refine ⟨core, hcompact, fun _ => Iff.rfl, ?_⟩
    intro y hy
    have hphys : y.val ∈ h.ball (j p0) A := by
      have himage : y.val ∈ (Subtype.val : C → N) '' Metric.ball p A := ⟨y, hy, rfl⟩
      rwa [(terminalSourceComponent_balls h (j p0) p A).2.1] at himage
    have hsmallCover : h.ball (j p0) A ⊆ j.target := by
      intro z hz
      exact hcover (hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
    rw [← terminalSourceNormal_ball_image g h j hsource hmetric p0 A hsmallCover] at hphys
    obtain ⟨z, hz, hzy⟩ := hphys
    obtain ⟨i, w, hw, hwz⟩ := mem_iUnion.mp (cover.cover hz)
    let x : W := ⟨w, hcoreBall hw⟩
    refine mem_iUnion.mpr ⟨i, x, hw, ?_⟩
    apply Subtype.ext
    exact (congrArg j hwz).trans hzy

end PoincareConjecture.M47
