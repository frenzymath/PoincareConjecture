/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/ChartDirectionalNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Analysis.Parabolic.Quasilinear.Tensor.TensorFirstOrderGraph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Actual directional derivatives in native charts

Push a smooth tangent field forward by a native chart differential. Its
coordinates are smooth on the chart target. The scalar chain rule and
inverse-chart differential identities express native differentiation as a
finite first-order Euclidean operator with these actual coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u

namespace PoincareMT.TensorProbeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

def chartFieldOnSource (p : M) (V : SmoothField (n := n) (M := M)) (x : M) : ModelE :=
  mfderiv (𝓡 n) 𝓘(ℝ, ModelE) (chartAt ModelE p) x (V x)

def chartField (p : M) (V : SmoothField (n := n) (M := M)) (z : ModelE) : ModelE :=
  chartFieldOnSource p V ((chartAt ModelE p).symm z)

theorem contMDiffOn_chartFieldOnSource (p : M) (V : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ModelE) ∞ (chartFieldOnSource p V)
      (chartAt ModelE p).source := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  have he : ContMDiffOn (𝓡 n) 𝓘(ℝ, ModelE) ∞ e e.source :=
    contMDiffOn_chart (I := 𝓡 n) (x := p)
  have htan := he.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    e.open_source.uniqueMDiffOn
  have hsec := htan.comp V.contMDiff.contMDiffOn (fun x hx => hx)
  have hproj := (contMDiff_snd_tangentBundle_modelSpace ModelE 𝓘(ℝ, ModelE)).comp_contMDiffOn hsec
  change ContMDiffOn (𝓡 n) 𝓘(ℝ, ModelE) ∞
    (fun x => mfderivWithin (𝓡 n) 𝓘(ℝ, ModelE) e e.source x (V x)) e.source at hproj
  apply hproj.congr
  intro x hx
  change mfderiv (𝓡 n) 𝓘(ℝ, ModelE) e x (V x) =
    mfderivWithin (𝓡 n) 𝓘(ℝ, ModelE) e e.source x (V x)
  rw [mfderivWithin_of_isOpen e.open_source hx]

theorem contDiffOn_chartField (p : M) (V : SmoothField (n := n) (M := M)) :
    ContDiffOn ℝ ∞ (chartField p V) (chartAt ModelE p).target := by
  have hcomp := (contMDiffOn_chartFieldOnSource p V).comp
    (contMDiffOn_chart_symm (I := 𝓡 n) (x := p)) (chartAt ModelE p).symm.mapsTo
  exact hcomp.contDiffOn

theorem contDiffOn_chartField_coordinate (p : M) (V : SmoothField (n := n) (M := M))
    (i : Fin n) : ContDiffOn ℝ ∞ (fun z => chartField p V z i) (chartAt ModelE p).target :=
  (contDiffOn_piLp 2).mp (contDiffOn_chartField p V) i

theorem contDiffOn_scalar_chartInverse (p : M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (f ∘ (chartAt ModelE p).symm) (chartAt ModelE p).target :=
  (hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn

/-- The native directional derivative is the actual coordinate first-order operator. -/
theorem directional_eq_chart_firstOrder (p : M) (V : SmoothField (n := n) (M := M))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {z : ModelE} (hz : z ∈ (chartAt ModelE p).target) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f ((chartAt ModelE p).symm z)
        (V ((chartAt ModelE p).symm z)) =
      ∑ i, chartField p V z i *
        fderiv ℝ (f ∘ (chartAt ModelE p).symm) z ((PiLp.basisFun 2 ℝ (Fin n)) i) := by
  let e : OpenPartialHomeomorph M ModelE := chartAt ModelE p
  have he : e.MDifferentiable (𝓡 n) 𝓘(ℝ, ModelE) :=
    mdifferentiable_chart (I := 𝓡 n) p
  have hinv := he.symm_comp_deriv (e.map_target hz)
  rw [e.right_inv hz] at hinv
  have hvinv : mfderiv 𝓘(ℝ, ModelE) (𝓡 n) e.symm z (chartField p V z) =
      V (e.symm z) := by
    have h := congrArg (fun L => L (V (e.symm z))) hinv
    change mfderiv 𝓘(ℝ, ModelE) (𝓡 n) e.symm z
      (mfderiv (𝓡 n) 𝓘(ℝ, ModelE) e (e.symm z) (V (e.symm z))) = V (e.symm z) at h
    exact h
  have hdirection : fderiv ℝ (f ∘ e.symm) z (chartField p V z) =
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z) (V (e.symm z)) := by
    have hchain := mfderiv_comp_apply z
      ((hf (e.symm z)).mdifferentiableAt (by simp))
      (he.mdifferentiableAt_symm hz) (chartField p V z)
    rw [mfderiv_eq_fderiv] at hchain
    exact hchain.trans (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm z)) hvinv)
  have hsum : (∑ i, chartField p V z i • (PiLp.basisFun 2 ℝ (Fin n)) i) =
      chartField p V z := by
    simpa only [PiLp.basisFun_repr] using
      (PiLp.basisFun 2 ℝ (Fin n)).sum_repr (chartField p V z)
  calc
    _ = fderiv ℝ (f ∘ e.symm) z (chartField p V z) := hdirection.symm
    _ = fderiv ℝ (f ∘ e.symm) z
        (∑ i, chartField p V z i • (PiLp.basisFun 2 ℝ (Fin n)) i) :=
      congrArg (fderiv ℝ (f ∘ e.symm) z) hsum.symm
    _ = _ := by
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl

end PoincareMT.TensorProbeNative
