import PoincareConjecture.Proofs.M09.InverseChartVector
import PoincareConjecture.Proofs.M09.SquareTimeDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def squareChartMetric {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (z : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - z.1 ^ 2)).toRiemannianMetric⟩
  let c := (chartAt E p).symm
  let L : E →L[ℝ] TangentSpace (𝓡 n) (c z.2) := mfderiv (𝓡 n) (𝓡 n) c z.2
  exact ((F.metric (T - z.1 ^ 2)).inner (c z.2)).bilinearComp L L

noncomputable def squareChartScalar {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (z : ℝ × E) : ℝ :=
  (F.connection (T - z.1 ^ 2)).scalarCurvature ((chartAt E p).symm z.2)

theorem squareChartMetric_symm {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (z : ℝ × E) (u v : E) :
    squareChartMetric F T p z u v = squareChartMetric F T p z v u :=
  (F.metric (T - z.1 ^ 2)).symm _ _ _

theorem squareChartMetric_pos {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (z : ℝ × E) (hz : z.2 ∈ (chartAt E p).target)
    (v : E) (hv : v ≠ 0) : 0 < squareChartMetric F T p z v v := by
  apply (F.metric (T - z.1 ^ 2)).pos
  intro h
  apply hv
  apply (inverseChartDifferential_bijective p z.2 hz).1
  exact h.trans (map_zero (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm z.2)).symm

theorem squareChartMetric_smooth {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J) (p : M) :
    ContDiffOn ℝ ∞ (squareChartMetric F T p)
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target) := by
  let S := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm
  have hsnd : ContMDiff (𝓘(ℝ, ℝ × E)) (𝓡 n) ∞ (Prod.snd : ℝ × E → E) :=
    contDiff_snd.contMDiff
  have hbase : ContMDiffOn (𝓘(ℝ, ℝ × E)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : ℝ × E ↦ (z.1, (chartAt E p).symm z.2)) S :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hc.comp hsnd.contMDiffOn (fun z hz ↦ hz.2))
  have hg := (squareTime_metric_smooth F T b hb hwindow).comp hbase
    (fun z hz ↦ ⟨hz.1, Set.mem_univ _⟩)
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have hu := (inverseChartVector_smooth p u).comp hsnd.contMDiffOn
    (fun z (hz : z ∈ S) ↦ hz.2)
  have hv := (inverseChartVector_smooth p v).comp hsnd.contMDiffOn
    (fun z (hz : z ∈ S) ↦ hz.2)
  have heval : ContMDiffOn (𝓘(ℝ, ℝ × E)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × E ↦ (⟨(chartAt E p).symm z.2, squareChartMetric F T p z u v⟩ :
        Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ))) S :=
    hg.clm_bundle_apply₂ hu hv
  have hscalar : ContMDiffOn (𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × E ↦ squareChartMetric F T p z u v) S := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval z hz)).2
  exact hscalar.contDiffOn

theorem squareChartScalar_smooth {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (p : M) :
    ContDiffOn ℝ ∞ (squareChartScalar F T p)
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target) := by
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm
  have hbase : ContMDiffOn (𝓘(ℝ, ℝ × E)) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun z : ℝ × E ↦ (z.1, (chartAt E p).symm z.2))
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hc.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz ↦ hz.2))
  exact ((squareTime_scalar_smooth F hM04 T b hb hwindow).comp hbase
    (fun z hz ↦ ⟨hz.1, Set.mem_univ _⟩)).contDiffOn

set_option backward.isDefEq.respectTransparency false in
theorem squareChartMetric_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (y u v : E) :
    HasDerivAt (fun r ↦ squareChartMetric F T p (r, y) u v)
      (4 * s * (F.connection (T - s ^ 2)).ricci ((chartAt E p).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y u)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v)) s := by
  exact squareTime_metric_hasDerivAt F T b hb hwindow s hs
    ((chartAt E p).symm y)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y u)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v)

end PoincareConjecture.Proofs.M09
