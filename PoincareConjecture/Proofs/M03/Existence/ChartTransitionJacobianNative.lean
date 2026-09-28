import PoincareConjecture.Proofs.M03.Existence.ChartMeasureUpperNative
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative

section Euclidean

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem contDiff_matrixDet :
    ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ => Matrix.det A) := by
  classical
  have hpoly : ContDiff ℝ ∞ (fun A : Fin n → Fin n → ℝ =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i) := by
    fun_prop
  simpa only [Matrix.det_apply'] using hpoly

theorem contDiff_clmDet : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => L.det) := by
  classical
  let b := PiLp.basisFun 2 ℝ (Fin n)
  have hmatrix : ContDiff ℝ ∞
      (fun L : E →L[ℝ] E => fun i j : Fin n => L (b j) i) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    have hv : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => L (b j)) :=
      contDiff_id.clm_apply contDiff_const
    exact (contDiff_piLp 2).mp hv i
  have heq : (fun L : E →L[ℝ] E => L.det) =
      (fun L : E →L[ℝ] E => Matrix.det (fun i j : Fin n => L (b j) i)) := by
    funext L
    change LinearMap.det L.toLinearMap = Matrix.det (fun i j : Fin n => L (b j) i)
    rw [← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    simp only [LinearMap.toMatrix_apply, b, PiLp.basisFun_repr]
    rfl
  rw [heq]
  exact contDiff_matrixDet.comp hmatrix

theorem isInvertible_fderiv_partialHomeomorph (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {z : E} (hz : z ∈ e.source) : (fderiv ℝ e z).IsInvertible := by
  have hf : DifferentiableAt ℝ e z :=
    (he.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ e.symm (e z) :=
    (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt (by simp)
  have hleft : e.symm ∘ e =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_source.mem_nhds hz] with y hy
    exact e.left_inv hy
  have hright : e ∘ e.symm =ᶠ[𝓝 (e z)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hz)] with y hy
    exact e.right_inv hy
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := fderiv ℝ e.symm (e z))
  · have hf' : DifferentiableAt ℝ e (e.symm (e z)) := by
      simpa only [e.left_inv hz] using hf
    have h := hright.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp (e z) hf' hg, e.left_inv hz, fderiv_id] at h
    exact h
  · have h := hleft.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp z hg hf, fderiv_id] at h
    exact h

theorem clm_det_ne_zero_of_isInvertible {L : E →L[ℝ] E} (hL : L.IsInvertible) : L.det ≠ 0 := by
  obtain ⟨e, he⟩ := hL
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

end Euclidean

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def chartTransition (p q : M) : OpenPartialHomeomorph E E :=
  (chartAt E p).symm.trans (chartAt E q)

@[simp] theorem chartTransition_apply (p q : M) (z : E) :
    chartTransition p q z = chartAt E q ((chartAt E p).symm z) := rfl

@[simp] theorem chartTransition_source (p q : M) :
    (chartTransition (n := n) p q).source = chartTransitionDomain (n := n) p q := rfl

@[simp] theorem chartTransition_target (p q : M) :
    (chartTransition (n := n) p q).target = chartTransitionDomain (n := n) q p := rfl

theorem chartTransition_contDiffOn (p q : M) :
    ContDiffOn ℝ ∞ (chartTransition (n := n) p q) (chartTransition (n := n) p q).source := by
  have he : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (chartAt E q) (chartAt E q).source :=
    contMDiffOn_chart (I := 𝓡 n) (x := q)
  have hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm (I := 𝓡 n) (x := p)
  exact (he.comp (hi.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn

theorem chartTransition_symm_contDiffOn (p q : M) :
    ContDiffOn ℝ ∞ (chartTransition (n := n) p q).symm (chartTransition (n := n) p q).target :=
  chartTransition_contDiffOn q p

theorem chartTransition_fderiv_invertible (p q : M) {z : E}
    (hz : z ∈ chartTransitionDomain p q) : (fderiv ℝ (chartTransition p q) z).IsInvertible :=
  isInvertible_fderiv_partialHomeomorph (chartTransition p q)
    (chartTransition_contDiffOn p q) (chartTransition_symm_contDiffOn p q) hz

def chartTransitionJacobian (p q : M) (z : E) : ℝ :=
  |(fderiv ℝ (chartTransition p q) z).det|

theorem chartTransitionJacobian_nonneg (p q : M) (z : E) :
    0 ≤ chartTransitionJacobian p q z := abs_nonneg _

theorem chartTransitionJacobian_pos (p q : M) {z : E}
    (hz : z ∈ chartTransitionDomain p q) : 0 < chartTransitionJacobian p q z :=
  abs_pos.mpr (clm_det_ne_zero_of_isInvertible (chartTransition_fderiv_invertible p q hz))

theorem chartTransitionJacobian_contDiffOn (p q : M) :
    ContDiffOn ℝ ∞ (chartTransitionJacobian (n := n) p q) (chartTransitionDomain (n := n) p q) := by
  have hd : ContDiffOn ℝ ∞ (fun z : E => (fderiv ℝ (chartTransition p q) z).det)
      (chartTransitionDomain (n := n) p q) :=
    contDiff_clmDet.comp_contDiffOn ((chartTransition_contDiffOn p q).fderiv_of_isOpen
      (chartTransition p q).open_source (by simp))
  exact hd.abs (fun z hz =>
    clm_det_ne_zero_of_isInvertible (chartTransition_fderiv_invertible p q hz))

theorem chartTransition_map_withDensity (p q : M) :
    Measure.map (chartTransition (n := n) p q)
      ((volume.restrict (chartTransitionDomain (n := n) p q)).withDensity
        (fun z => ENNReal.ofReal (chartTransitionJacobian (n := n) p q z))) =
      volume.restrict (chartTransitionDomain (n := n) q p) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume
    (chartTransition (n := n) p q).open_source.measurableSet.nullMeasurableSet
    (fun z hz => ((chartTransition_contDiffOn p q).contDiffAt
      ((chartTransition p q).open_source.mem_nhds hz)).differentiableAt
        (by simp) |>.hasFDerivAt.hasFDerivWithinAt)
    (chartTransition (n := n) p q).injOn
  have hi : (chartTransition (n := n) p q) '' (chartTransition (n := n) p q).source =
      (chartTransition (n := n) p q).target :=
    PartialEquiv.image_source_eq_target (chartTransition (n := n) p q).toPartialEquiv
  rw [hi] at h
  exact h

end PoincareConjecture.ChartMeasureNative
