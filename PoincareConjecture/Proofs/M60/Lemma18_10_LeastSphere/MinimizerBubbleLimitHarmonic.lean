import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitInversion
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitEquation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ


def SUPlaneHarmonic (g : RiemannianMetric n M) (f : LoopPlane → M) : Prop :=
  ∀ p z, f z ∈ (extChartAt (𝓡 n) p).source →
    let u := extChartAt (𝓡 n) p ∘ f
    let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
    ∑ i : Fin 2, covDerivAlong Gamma u (fun y => fderiv ℝ u y (b i)) (b i) z = 0




theorem suHarmonic_change_target (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (p q : M) (z : LoopPlane)
    (hp : f z ∈ (extChartAt (𝓡 n) p).source)
    (hq : f z ∈ (extChartAt (𝓡 n) q).source)
    (hzero : let u := extChartAt (𝓡 n) p ∘ f
      let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
      ∑ i : Fin 2, covDerivAlong Gamma u (fun y => fderiv ℝ u y (b i)) (b i) z = 0) :
    let u := extChartAt (𝓡 n) q ∘ f
    let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) q).symm)
    ∑ i : Fin 2, covDerivAlong Gamma u (fun y => fderiv ℝ u y (b i)) (b i) z = 0 := by
  let cp := extChartAt (𝓡 n) p
  let cq := extChartAt (𝓡 n) q
  let u := cp ∘ f
  let w := cq ∘ f
  let T := cq ∘ cp.symm
  let Gp := christoffelBilinear (g.pullbackCoefficients cp.symm)
  let Gq := christoffelBilinear (g.pullbackCoefficients cq.symm)
  have hu {y : LoopPlane} (hy : f y ∈ cp.source) : ContDiffAt ℝ ∞ u y :=
    contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (x := p) (n := ∞)
        (by simpa only [cp, extChartAt_source] using hy)).comp y (hf y))
  have hsource : ∀ᶠ y in 𝓝 z, f y ∈ cp.source ∧ f y ∈ cq.source := by
    filter_upwards [hf.continuous.continuousAt ((isOpen_extChartAt_source p).mem_nhds hp),
      hf.continuous.continuousAt ((isOpen_extChartAt_source q).mem_nhds hq)] with y hyp hyq
    exact ⟨hyp, hyq⟩
  have hgerm {y : LoopPlane} (hy : f y ∈ cp.source) : T ∘ u =ᶠ[𝓝 y] w := by
    filter_upwards [hf.continuous.continuousAt
      ((isOpen_extChartAt_source p).mem_nhds hy)] with x hx
    exact congrArg cq (cp.left_inv hx)
  have hfield (i : Fin 2) :
      (fun y => fderiv ℝ T (u y) (fderiv ℝ u y (b i))) =ᶠ[𝓝 z]
        (fun y => fderiv ℝ w y (b i)) := by
    filter_upwards [hsource] with y hy
    have hqi : cp.symm (u y) ∈ cq.source := by
      change cp.symm (cp (f y)) ∈ cq.source
      rw [cp.left_inv hy.1]
      exact hy.2
    have hT : ContDiffAt ℝ ∞ T (u y) := contMDiffAt_iff_contDiffAt.mp
      ((contMDiffAt_extChartAt' (x := q) (n := ∞)
        (by simpa only [cq, extChartAt_source] using hqi)).comp _
          ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
            ((isOpen_extChartAt_target p).mem_nhds (cp.map_source hy.1))))
    have hd := (hgerm hy.1).fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp y (hT.differentiableAt (by simp)) ((hu hy.1).differentiableAt (by simp))] at hd
    exact congrArg (fun A : LoopPlane →L[ℝ] E => A (b i)) hd
  have hterm (i : Fin 2) :
      covDerivAlong Gq w (fun y => fderiv ℝ w y (b i)) (b i) z =
        fderiv ℝ T (u z) (covDerivAlong Gp u (fun y => fderiv ℝ u y (b i)) (b i) z) := by
    have h := covDerivAlong_chart_change (P := LoopPlane) (u := u)
      (V := fun y => fderiv ℝ u y (b i)) (p := z) g p q (cp.map_source hp)
      (by change cp.symm (cp (f z)) ∈ cq.source; rw [cp.left_inv hp]; exact hq)
      ((hu hp).differentiableAt (by simp))
      (((hu hp).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiffAt_const |>.differentiableAt (by simp)) (b i)
    change covDerivAlong Gq (T ∘ u)
      (fun y => fderiv ℝ T (u y) (fderiv ℝ u y (b i))) (b i) z = _ at h
    rw [covDerivAlong_congr_base Gq _ (hgerm hp), covDerivAlong_congr Gq w (hfield i)] at h
    exact h
  change (∑ i : Fin 2, covDerivAlong Gq w (fun y => fderiv ℝ w y (b i)) (b i) z) = 0
  simp_rw [hterm]
  have hzero' : (∑ i : Fin 2, covDerivAlong Gp u
      (fun y => fderiv ℝ u y (b i)) (b i) z) = 0 := hzero
  rw [← map_sum, hzero', map_zero]



theorem suHarmonic_inversion (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (hh : SUPlaneHarmonic g f)
    (p : M) {z : LoopPlane} (hz : z ≠ 0)
    (hp : f (suBubbleInversion z) ∈ (extChartAt (𝓡 n) p).source) :
    let u := extChartAt (𝓡 n) p ∘ (f ∘ suBubbleInversion)
    let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
    ∑ i : Fin 2, covDerivAlong Gamma u (fun y => fderiv ℝ u y (b i)) (b i) z = 0 := by
  let u := extChartAt (𝓡 n) p ∘ f
  let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
  have hu : ContDiffAt ℝ ∞ u (suBubbleInversion z) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (x := p) (n := ∞)
      (by simpa only [extChartAt_source] using hp)).comp _ (hf _))
  have hu2 : ContDiffAt ℝ 2 u (suBubbleInversion z) :=
    hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hi := suBubbleInversion_geometry hz
  have hi2 := hi.1.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hcomp := hu2.comp z hi2
  have hbase := hh p (suBubbleInversion z) hp
  change (∑ i : Fin 2, covDerivAlong Gamma u
    (fun y => fderiv ℝ u y (b i)) (b i) (suBubbleInversion z)) = 0 at hbase
  simp only [Fin.sum_univ_two, covDerivAlong, fderiv_column hu2] at hbase
  have h := covariant_laplacian_comp_eq_zero Gamma hu2 hi2
    (show 0 < (2 / ‖z‖) ^ 4 by positivity) hi.2.2.1 (suBubbleInversion_laplacian hz)
    (by convert hbase using 1; abel)
  change (∑ i : Fin 2, covDerivAlong Gamma (u ∘ suBubbleInversion)
    (fun y => fderiv ℝ (u ∘ suBubbleInversion) y (b i)) (b i) z) = 0
  simp only [Fin.sum_univ_two, covDerivAlong, fderiv_column hcomp]
  convert h using 1; abel

end PoincareConjecture.M60
