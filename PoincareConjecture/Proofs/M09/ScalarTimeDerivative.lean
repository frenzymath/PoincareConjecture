import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Analysis.Calculus.Deriv.Comp








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax τ s : ℝ}

theorem backward_scalar_hasDerivWithinAt (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hmax : τ ≤ τmax)
    (hs : s ∈ Set.Icc 0 τ) (x : M) :
    HasDerivWithinAt (fun r ↦ (F.connection (T - r)).scalarCurvature x)
      (-((F.connection (T - s)).laplacian (F.connection (T - s)).scalarCurvature x +
        2 * (F.connection (T - s)).ricciNormSq x)) (Set.Icc 0 τ) s := by
  have hmap : Set.MapsTo (fun r : ℝ ↦ T - r) (Set.Icc 0 τ) J := by
    intro r hr
    exact hwindow ⟨sub_le_sub_left (hr.2.trans hmax) T, sub_le_self T hr.1⟩
  have hevolution := hM04.scalar_evolution n M J F (T - s) (hmap hs) x
  have hclock : HasDerivWithinAt (fun r : ℝ ↦ T - r) (-1) (Set.Icc 0 τ) s := by
    simpa using ((hasDerivAt_id s).const_sub T).hasDerivWithinAt
  simpa only [Function.comp_def, mul_neg_one] using hevolution.comp s hclock hmap

theorem regular_scalar_derivative_eq (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Set.Icc (T - τmax) T ⊆ J) {p q : M}
    (r : ReducedLengthRegularPoint F T τmax p q τ) (hs : s ∈ Set.Ioo 0 τ) :
    r.path_scalar_time_derivative s =
      -((F.connection (T - s)).laplacian (F.connection (T - s)).scalarCurvature
          (r.path.curve s) + 2 * (F.connection (T - s)).ricciNormSq (r.path.curve s)) := by
  have hmem : s ∈ Set.Icc 0 τ := ⟨hs.1.le, hs.2.le⟩
  have hspec := r.path_scalar_time_derivative_spec s hs
  have hback := backward_scalar_hasDerivWithinAt (F := F) hM04 hwindow r.tau_lt.le
    hmem (r.path.curve s)
  have hunique := (uniqueDiffOn_Icc r.tau_pos) s hmem
  exact (hspec.derivWithin hunique).symm.trans (hback.derivWithin hunique)

end PoincareConjecture.Proofs.M09
