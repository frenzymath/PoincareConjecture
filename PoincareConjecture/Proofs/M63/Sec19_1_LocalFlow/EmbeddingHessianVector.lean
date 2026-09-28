import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackMetricHessian
import Mathlib.Analysis.Calculus.ContDiff.WithLp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ ι

noncomputable def coordinateHessian {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (e : M → W) (p : M)
    (v w : TangentSpace (𝓡 n) p) : W :=
  WithLp.toLp 2 (fun i => D.hessian (fun q => e q i) p v w)

theorem coordinateHessian_eq_chart {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    (p q : M) (hq : q ∈ (chartAt E p).source) (u v : E) :
    let f : E → W := e ∘ (chartAt E p).symm
    coordinateHessian D e q (chartVectorField p u q) (chartVectorField p v q) =
      fderiv ℝ (fderiv ℝ f) ((chartAt E p) q) u v -
        fderiv ℝ f ((chartAt E p) q)
          (coordinateChristoffel (g.pullbackCoefficients (chartAt E p).symm)
            ((chartAt E p) q) u v) := by
  let c := chartAt E p
  let f : E → W := e ∘ c.symm
  have hy : c q ∈ c.target := c.map_source hq
  have hf : ContDiffOn ℝ ∞ f c.target :=
    (he.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn
  ext i
  let L : W →L[ℝ] ℝ := EuclideanSpace.proj i
  let A : (E →L[ℝ] W) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.compL ℝ E W ℝ L
  have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => e x i) :=
    L.contDiff.contMDiff.comp he
  have hD (y : E) (hy : y ∈ c.target) :
      fderiv ℝ (L ∘ f) y = A (fderiv ℝ f y) :=
    (L.hasFDerivAt.comp y
      ((hf.contDiffAt (c.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hDDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (c q)) (c q) :=
    (((hf.contDiffAt (c.open_target.mem_nhds hy)).fderiv_right (m := ∞)
      (by simp)).differentiableAt (by simp)).hasFDerivAt
  have heq : fderiv ℝ (L ∘ f) =ᶠ[𝓝 (c q)] A ∘ fderiv ℝ f := by
    filter_upwards [c.open_target.mem_nhds hy] with y hyt
    exact hD y hyt
  have hDD : fderiv ℝ (fderiv ℝ (L ∘ f)) (c q) =
      A.comp (fderiv ℝ (fderiv ℝ f) (c q)) :=
    ((A.hasFDerivAt.comp (c q) hDDf).congr_of_eventuallyEq heq).fderiv
  have hh := hessian_eq_chart_christoffel D hei p q hq u v
  change D.hessian (fun x => e x i) q (chartVectorField p u q) (chartVectorField p v q) =
    fderiv ℝ (fderiv ℝ (L ∘ f)) (c q) u v -
      fderiv ℝ (L ∘ f) (c q)
        (coordinateChristoffel (g.pullbackCoefficients c.symm) (c q) u v) at hh
  rw [hD _ hy, hDD] at hh
  exact hh

theorem flow_coordinateHessian_pullback_contDiffOn {a b : ℝ}
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set V} (hU : IsOpen U) {ρ : V → M}
    (hρ : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ ρ U) :
    ContDiffOn ℝ ∞
      (fun z : (ℝ × V) × V => coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)
        (mfderiv 𝓘(ℝ, V) (𝓡 n) ρ z.1.2 z.2)) ((Icc a b ×ˢ U) ×ˢ univ) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => e x i) :=
    (EuclideanSpace.proj i).contDiff.contMDiff.comp he
  exact (flow_pullback_metric_hessian_contDiffOn F hU hρ hei).2

end PoincareConjecture.M63
