import PoincareConjecture.Proofs.M09.EndpointComparisonAction
import PoincareConjecture.Proofs.M09.PathComparison
import PoincareConjecture.Definitions.Ch06.ReducedLength
import Mathlib.Geometry.Manifold.Algebra.LieGroup








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

theorem exists_smooth_upperBarrier {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p q : M) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    Nonempty (ReducedLengthUpperBarrier F T p q b) := by
  obtain ⟨N, hN, hqN, hNt, A, hA, hAq, hpaths⟩ :=
    exists_local_smooth_comparison_action F hM04 T τmax hτmax hwindow hL p q b hb hmax
  let C : M × ℝ → ℝ := fun w ↦ A w / (2 * Real.sqrt w.2)
  have hC : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞ C N := by
    intro w hw
    have ht := (hNt hw).2.1
    have hroot : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
        (fun z : M × ℝ ↦ Real.sqrt z.2) w :=
      (Real.contDiffAt_sqrt ht.ne').contMDiffAt.comp w contMDiffAt_snd
    exact ((hA.contMDiffAt (hN.mem_nhds hw)).div₀ (contMDiffAt_const.mul hroot)
      (mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr ht).ne')).contMDiffWithinAt
  have hcenter := hC.contMDiffAt (hN.mem_nhds hqN)
  have htime : ∃ d : ℝ, HasDerivAt (fun s ↦ C (q, s)) d b := by
    have h := (hcenter.comp b (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt
    exact ⟨_, (h.differentiableAt (by simp)).hasDerivAt⟩
  refine ⟨{
    neighborhood := N
    neighborhood_open := hN
    center_mem := hqN
    representative := C
    touches := ?_
    dominates := ?_
    representative_spacetime_smooth := hcenter
    representative_space_smooth_on := hC.comp
      (contMDiffOn_id.prodMk contMDiffOn_const) (fun x hx ↦ hx)
    representative_space_smooth := hcenter.comp q
      (contMDiffAt_id.prodMk contMDiffAt_const)
    representative_time_derivative := htime }⟩
  · change A (q, b) / (2 * Real.sqrt b) = _
    rw [hAq, mul_div_cancel_left₀ _ (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).ne']
  · intro w hw
    obtain ⟨P, hP0, hPw, hPA⟩ := hpaths w hw
    have hle := reducedLength_le_path hL (hNt hw).2.1 (hNt hw).2.2.le P hP0 hPw
    rwa [hPA] at hle

end PoincareConjecture.Proofs.M09
