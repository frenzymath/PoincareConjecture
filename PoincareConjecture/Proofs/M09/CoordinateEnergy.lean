import PoincareConjecture.Proofs.M09.SquareChartPairing
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

section Coordinate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem coordinateEnergy_hasDerivAt
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ)
    (a v : ℝ → E) (s : ℝ) (hG : DifferentiableAt ℝ G (s, a s))
    (hsymm : ∀ u w : E, G (s, a s) u w = G (s, a s) w u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < G (s, a s) u u)
    (ha : HasDerivAt a (v s) s)
    (hv : HasDerivAt v (regularizedCoordinatePhase G R (s, (a s, v s))).2 s) :
    HasDerivAt (fun r ↦ G (r, a r) (v r) (v r))
      (4 * s ^ 2 * fderiv ℝ R (s, a s) (0, v s) -
        fderiv ℝ G (s, a s) (1, 0) (v s) (v s)) s := by
  have hGt := hG.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk ha)
  have henergy := (hGt.clm_apply hv).clm_apply hv
  have henergy' : HasDerivAt (fun r ↦ G (r, a r) (v r) (v r))
      (fderiv ℝ G (s, a s) (1, v s) (v s) (v s) +
        G (s, a s) (regularizedCoordinatePhase G R (s, (a s, v s))).2 (v s) +
        G (s, a s) (v s) (regularizedCoordinatePhase G R (s, (a s, v s))).2) s := by
    simpa only [Function.comp_apply, Function.id_def, add_apply] using henergy
  have hphase := regularizedCoordinatePhase_pairing G R (s, a s) hpos (v s) (v s)
  have hsplit : fderiv ℝ G (s, a s) (1, v s) (v s) (v s) =
      fderiv ℝ G (s, a s) (1, 0) (v s) (v s) +
        fderiv ℝ G (s, a s) (0, v s) (v s) (v s) := by
    rw [show (1, v s) = ((1 : ℝ), (0 : E)) + (0, v s) by simp,
      map_add, add_apply, add_apply]
  apply henergy'.congr_deriv
  rw [hsplit, hsymm (v s) (regularizedCoordinatePhase G R (s, (a s, v s))).2]
  dsimp only at hphase
  linarith

end Coordinate

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem squareChartEnergy_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (a v : ℝ → E) (s : ℝ)
    (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hy : a s ∈ (chartAt E p).target) (ha : HasDerivAt a (v s) s)
    (hv : HasDerivAt v
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a s, v s))).2 s) :
    HasDerivAt (fun r ↦ squareChartMetric F T p (r, a r) (v r) (v r))
      (4 * s ^ 2 *
          mvfderiv (𝓡 n) (fun x ↦ (F.connection (T - s ^ 2)).scalarCurvature x)
            ((chartAt E p).symm (a s))
            (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s) (v s)) -
        4 * s * (F.connection (T - s ^ 2)).ricci ((chartAt E p).symm (a s))
          (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s) (v s))
          (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s) (v s))) s := by
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, a s) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
      ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)).differentiableAt
      (by simp)
  have h := coordinateEnergy_hasDerivAt (squareChartMetric F T p) (squareChartScalar F T p)
    a v s hG (squareChartMetric_symm F T p (s, a s))
    (squareChartMetric_pos F T p (s, a s) hy) ha hv
  rw [squareChartScalar_space_pairing F hM04 T b hb hwindow p s hs (a s) (v s) hy,
    squareChartMetric_time_pairing F T b hb hwindow p s hs (a s) (v s) (v s) hy] at h
  exact h

end PoincareConjecture.Proofs.M09
