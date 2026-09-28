import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

open Proofs.M58

theorem m64Polar_basis_expansion (i : Fin 2) (t : ℝ) :
    (angularPoint t) i • angularPoint t + (angularVector t) i • angularVector t =
      EuclideanSpace.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [angularPoint, angularVector] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem m64AngularVector_component_contDiff (i : Fin 2) :
    ContDiff ℝ 1 (fun t => angularVector t i) := by
  fin_cases i
  · simpa [angularVector] using Real.contDiff_sin.neg.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  · simpa [angularVector] using Real.contDiff_cos.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)

theorem m64AngularVector_component_hasDerivAt (i : Fin 2) (t : ℝ) :
    HasDerivAt (fun s => angularVector s i) (-angularPoint t i) t := by
  fin_cases i
  · simpa +instances [angularVector, angularPoint] using! (Real.hasDerivAt_sin t).neg
  · simpa +instances [angularVector, angularPoint] using! Real.hasDerivAt_cos t

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def m64DiskRadialFlux (f : LoopPlane → E) (i : Fin 2) (p : ℝ × ℝ) : E :=
  (p.1 * angularPoint p.2 i) • f (p.1 • angularPoint p.2)

def m64DiskAngularFlux (f : LoopPlane → E) (i : Fin 2) (p : ℝ × ℝ) : E :=
  angularVector p.2 i • f (p.1 • angularPoint p.2)

theorem m64DiskFlux_contDiff {f : LoopPlane → E} (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    ContDiff ℝ 1 (m64DiskRadialFlux f i) ∧ ContDiff ℝ 1 (m64DiskAngularFlux f i) := by
  have hp : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 • angularPoint p.2) :=
    contDiff_fst.smul ((contDiff_angularPoint.of_le (by simp)).comp contDiff_snd)
  have hc : ContDiff ℝ 1 (fun t => angularPoint t i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (contDiff_angularPoint.of_le (by simp))
  exact ⟨(contDiff_fst.mul (hc.comp contDiff_snd)).smul (hf.comp hp),
    ((m64AngularVector_component_contDiff i).comp contDiff_snd).smul (hf.comp hp)⟩

theorem m64DiskFlux_divergence {f : LoopPlane → E} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (p : ℝ × ℝ) :
    fderiv ℝ (m64DiskRadialFlux f i) p (1, 0) +
      fderiv ℝ (m64DiskAngularFlux f i) p (0, 1) =
        p.1 • fderiv ℝ f (p.1 • angularPoint p.2) (EuclideanSpace.single i 1) := by
  obtain ⟨hR, hT⟩ := m64DiskFlux_contDiff hf i
  have hrad : HasDerivAt (fun r : ℝ => r • angularPoint p.2) (angularPoint p.2) p.1 := by
    simpa +instances only [one_smul, id_eq] using!
      (hasDerivAt_id p.1).smul_const (angularPoint p.2)
  have hfr := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt p.1 hrad
  have hr0 := ((hasDerivAt_id p.1).mul_const (angularPoint p.2 i)).smul hfr
  have hr1 := (hR.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hr : fderiv ℝ (m64DiskRadialFlux f i) p (1, 0) =
      (p.1 * angularPoint p.2 i) • fderiv ℝ f (p.1 • angularPoint p.2) (angularPoint p.2) +
        angularPoint p.2 i • f (p.1 • angularPoint p.2) := by
    simpa only [one_mul, id_eq, Function.comp_def] using hr1.unique hr0
  have hang := (hasDerivAt_angularPoint p.2).const_smul p.1
  have hft := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt p.2 hang
  have ht0 := (m64AngularVector_component_hasDerivAt i p.2).smul hft
  have ht1 := (hT.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have ht : fderiv ℝ (m64DiskAngularFlux f i) p (0, 1) =
      angularVector p.2 i • fderiv ℝ f (p.1 • angularPoint p.2) (p.1 • angularVector p.2) +
        (-angularPoint p.2 i) • f (p.1 • angularPoint p.2) := ht1.unique ht0
  rw [hr, ht, map_smul, ← m64Polar_basis_expansion i p.2, map_add, map_smul, map_smul]
  module

theorem m64DiskAngularFlux_endpoints (f : LoopPlane → E) (i : Fin 2) (r : ℝ) :
    m64DiskAngularFlux f i (r, Real.pi) = m64DiskAngularFlux f i (r, -Real.pi) := by
  have ha : angularPoint Real.pi = angularPoint (-Real.pi) := by
    ext j
    fin_cases j <;> simp [angularPoint]
  have hv : angularVector Real.pi = angularVector (-Real.pi) := by
    ext j
    fin_cases j <;> simp [angularVector]
  simp only [m64DiskAngularFlux, ha, hv]

end PoincareConjecture
