import PoincareConjecture.Proofs.M09.CoordinateConnectionBilinear
import PoincareConjecture.Proofs.M09.TimeSpaceDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
theorem coordinateConnection_time_pairing
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (s : ℝ) (y : E) (hz : (s, y) ∈ U) (v w u : E) :
    let C := coordinateConnectionBilinear G
    let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ fderiv ℝ G (s, x) (1, 0)
    G (s, y) (fderiv ℝ C (s, y) (1, 0) v w) u =
      (1 / 2 : ℝ) * (fderiv ℝ H y v w u + fderiv ℝ H y w v u - fderiv ℝ H y u v w) -
        H y (C (s, y) v w) u := by
  let C := coordinateConnectionBilinear G
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ fderiv ℝ G (s, x) (1, 0)
  have hGa := hG.contDiffAt (hU.mem_nhds hz)
  have hCa : ContDiffAt ℝ ∞ C (s, y) :=
    (coordinateConnectionBilinear_contDiffOn G U hU hG hpos).contDiffAt
    (hU.mem_nhds hz)
  have hGt : HasDerivAt (fun r ↦ G (r, y)) (fderiv ℝ G (s, y) (1, 0)) s :=
    (hGa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
  have hCt0 := (hCa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
  have hCt : HasDerivAt (C ∘ fun r : ℝ ↦ (r, y))
      (fderiv ℝ C (s, y) (1, 0)) s := hCt0
  have hCvw0 := (hCt.clm_apply (hasDerivAt_const s v)).clm_apply (hasDerivAt_const s w)
  have hCvw : HasDerivAt (fun r ↦ C (r, y) v w)
      (fderiv ℝ C (s, y) (1, 0) v w) s := by
    simpa only [Function.comp_def, map_zero, add_zero, zero_apply] using hCvw0
  have hleft : HasDerivAt (fun r ↦ G (r, y) (C (r, y) v w) u)
      (G (s, y) (fderiv ℝ C (s, y) (1, 0) v w) u + H y (C (s, y) v w) u) s := by
    simpa [H, add_comm] using (hGt.clm_apply hCvw).clm_apply (hasDerivAt_const s u)
  have hfirst : HasDerivAt (fun r ↦ fderiv ℝ G (r, y) (0, v) w u)
      (fderiv ℝ H y v w u) s := by
    simpa only [map_zero, add_zero] using
      ((hasDerivAt_spatialDerivative_time G s y v hGa).clm_apply
        (hasDerivAt_const s w)).clm_apply (hasDerivAt_const s u)
  have hsecond : HasDerivAt (fun r ↦ fderiv ℝ G (r, y) (0, w) v u)
      (fderiv ℝ H y w v u) s := by
    simpa only [map_zero, add_zero] using
      ((hasDerivAt_spatialDerivative_time G s y w hGa).clm_apply
        (hasDerivAt_const s v)).clm_apply (hasDerivAt_const s u)
  have hthird : HasDerivAt (fun r ↦ fderiv ℝ G (r, y) (0, u) v w)
      (fderiv ℝ H y u v w) s := by
    simpa only [map_zero, add_zero] using
      ((hasDerivAt_spatialDerivative_time G s y u hGa).clm_apply
        (hasDerivAt_const s v)).clm_apply (hasDerivAt_const s w)
  have hright := ((hfirst.add hsecond).sub hthird).const_mul (1 / 2 : ℝ)
  have heq : (fun r ↦ G (r, y) (C (r, y) v w) u) =ᶠ[𝓝 s]
      (fun r ↦ (1 / 2 : ℝ) * (fderiv ℝ G (r, y) (0, v) w u +
        fderiv ℝ G (r, y) (0, w) v u - fderiv ℝ G (r, y) (0, u) v w)) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hz)] with r hr
    exact coordinateConnection_pairing G (r, y) (hpos (r, y) hr) v w u
  have h := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  linarith

end PoincareConjecture.Proofs.M09
