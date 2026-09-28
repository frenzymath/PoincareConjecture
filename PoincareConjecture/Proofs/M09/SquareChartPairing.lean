import PoincareConjecture.Proofs.M09.SquareChartMetric
import PoincareConjecture.Proofs.M09.ChartVectorField
import PoincareConjecture.Proofs.M09.CoordinatePhase
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM









set_option autoImplicit false
set_option maxSynthPendingDepth 3

set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartMetricPairing_smooth (g : RiemannianMetric n M) (p : M) (u v : E) :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ g.inner x (chartVectorField p u x) (chartVectorField p v x))
      (chartAt E p).source := by
  have heval := g.contMDiff.contMDiffOn.clm_bundle_apply₂
    (chartVectorField_smooth p u) (chartVectorField_smooth p v)
  intro x hx
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval x hx)).2

theorem squareChartMetric_space_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y u v w : E) (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (squareChartMetric F T p) (s, y) (0, w) u v =
      mvfderiv (𝓡 n)
        (fun x ↦ (F.metric (T - s ^ 2)).inner x
          (chartVectorField p u x) (chartVectorField p v x)) ((chartAt E p).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) := by
  let f : M → ℝ := fun x ↦ (F.metric (T - s ^ 2)).inner x
    (chartVectorField p u x) (chartVectorField p v x)
  have hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f ((chartAt E p).symm y) :=
    ((chartMetricPairing_smooth (F.metric (T - s ^ 2)) p u v).contMDiffAt
      ((chartAt E p).open_source.mem_nhds ((chartAt E p).map_target hy))).mdifferentiableAt
      (by simp)
  have hchain := mvfderiv_chartVectorField p f y w hy hf
  rw [chartVectorField_at_inverse p w y hy] at hchain
  have heq : (fun z : E ↦ f ((chartAt E p).symm z)) =ᶠ[𝓝 y]
      (fun z ↦ squareChartMetric F T p (s, z) u v) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
    dsimp [f]
    rw [chartVectorField_at_inverse p u z hz, chartVectorField_at_inverse p v z hz]
    rfl
  rw [heq.fderiv_eq] at hchain
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, y) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
    ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)).differentiableAt
    (by simp)
  have hslice := hG.hasFDerivAt.comp y
    ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))
  have heval := (hslice.clm_apply (hasFDerivAt_const u y)).clm_apply
    (hasFDerivAt_const v y)
  have hcoord : fderiv ℝ (fun z ↦ squareChartMetric F T p (s, z) u v) y w =
      fderiv ℝ (squareChartMetric F T p) (s, y) (0, w) u v := by
    simpa [Function.comp_def] using congrArg (fun L : E →L[ℝ] ℝ ↦ L w) heval.fderiv
  exact hcoord.symm.trans hchain.symm

theorem squareChartMetric_time_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y u v : E) (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (squareChartMetric F T p) (s, y) (1, 0) u v =
      4 * s * (F.connection (T - s ^ 2)).ricci ((chartAt E p).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y u)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v) := by
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, y) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
    ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)).differentiableAt
    (by simp)
  have hslice := hG.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
  have heval := (hslice.clm_apply (hasDerivAt_const s u)).clm_apply (hasDerivAt_const s v)
  have hmetric := squareChartMetric_hasDerivAt F T b hb hwindow p s hs y u v
  simpa using heval.unique hmetric

set_option backward.isDefEq.respectTransparency false in
theorem squareChartScalar_space_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y w : E) (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (squareChartScalar F T p) (s, y) (0, w) =
      mvfderiv (𝓡 n) (fun x ↦ (F.connection (T - s ^ 2)).scalarCurvature x)
        ((chartAt E p).symm y) (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) := by
  have hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x : M ↦ (F.connection (T - s ^ 2)).scalarCurvature x) := by
    have hbase : ContMDiff (𝓡 n) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
        (fun x : M ↦ (s, x)) := contMDiff_const.prodMk contMDiff_id
    have hbaseOn : ContMDiffOn (𝓡 n) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
        (fun x : M ↦ (s, x)) Set.univ := hbase.contMDiffOn
    have h := (squareTime_scalar_smooth F hM04 T b hb hwindow).comp
      hbaseOn (fun x _ ↦ ⟨hs, Set.mem_univ x⟩)
    exact contMDiffOn_univ.mp h
  have hchain := mvfderiv_chartVectorField p
    (fun x ↦ (F.connection (T - s ^ 2)).scalarCurvature x) y w hy
    ((hf _).mdifferentiableAt (by simp))
  rw [chartVectorField_at_inverse p w y hy] at hchain
  have hR : DifferentiableAt ℝ (squareChartScalar F T p) (s, y) :=
    ((squareChartScalar_smooth F hM04 T b hb hwindow p).contDiffAt
    ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)).differentiableAt
    (by simp)
  have hslice := hR.hasFDerivAt.comp y
    ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))
  have hcoord : fderiv ℝ (fun z ↦ squareChartScalar F T p (s, z)) y w =
      fderiv ℝ (squareChartScalar F T p) (s, y) (0, w) := by
    simpa [Function.comp_def] using congrArg (fun L : E →L[ℝ] ℝ ↦ L w) hslice.fderiv
  exact hcoord.symm.trans hchain.symm

set_option backward.isDefEq.respectTransparency false in
theorem regularizedCoordinatePhase_geometric_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y v w : E) (hy : y ∈ (chartAt E p).target) :
    (F.metric (T - s ^ 2)).inner ((chartAt E p).symm y)
        ((mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y)
          (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
            (s, (y, v))).2 +
          (F.connection (T - s ^ 2)).connection (chartVectorField p v) ((chartAt E p).symm y)
            (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v))
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) -
      2 * s ^ 2 * mvfderiv (𝓡 n) (fun x ↦ (F.connection (T - s ^ 2)).scalarCurvature x)
        ((chartAt E p).symm y) (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) +
      4 * s * (F.connection (T - s ^ 2)).ricci ((chartAt E p).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) = 0 := by
  have hphase := regularizedCoordinatePhase_pairing
    (squareChartMetric F T p) (squareChartScalar F T p) (s, y)
    (fun a ha ↦ squareChartMetric_pos F T p (s, y) hy a ha) v w
  rw [squareChartMetric_time_pairing F T b hb hwindow p s hs y v w hy,
    squareChartScalar_space_pairing F hM04 T b hb hwindow p s hs y w hy] at hphase
  have hkoszul := chartVectorField_diagonal_koszul
    (F.connection (T - s ^ 2)) p v w ((chartAt E p).symm y) ((chartAt E p).map_target hy)
  rw [chartVectorField_at_inverse p v y hy, chartVectorField_at_inverse p w y hy] at hkoszul
  rw [← squareChartMetric_space_pairing F T b hb hwindow p s hs y v w v hy,
    ← squareChartMetric_space_pairing F T b hb hwindow p s hs y v v w hy] at hkoszul
  change (F.metric (T - s ^ 2)).inner ((chartAt E p).symm y)
    ((mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y)
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (y, v))).2)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y w) = _ at hphase
  rw [map_add, ContinuousLinearMap.add_apply]
  linarith

end PoincareConjecture.Proofs.M09
