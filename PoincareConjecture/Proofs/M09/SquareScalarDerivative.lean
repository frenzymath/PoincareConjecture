import PoincareConjecture.Proofs.M09.ParametricCurveDerivative
import PoincareConjecture.Proofs.M09.ScalarTimeDerivative
import PoincareConjecture.Proofs.M09.SquareTimeFields








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem squareTime_scalar_along_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax b : ℝ)
    (hb : 0 < b) (hmax : b < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (α : ℝ → M) (s : ℝ) (hs : s ∈ Set.Ioo 0 (Real.sqrt b))
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    HasDerivAt (fun r ↦ (F.connection (T - r ^ 2)).scalarCurvature (α r))
      (2 * s * (-((F.connection (T - s ^ 2)).laplacian
          (F.connection (T - s ^ 2)).scalarCurvature (α s) +
            2 * (F.connection (T - s ^ 2)).ricciNormSq (α s))) +
        mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature (α s)
          (curveVelocity α s)) s := by
  have hτmax : 0 < τmax := hb.trans hmax
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans hs.1,
      hs.2.trans (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hf : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ))
      (fun z : ℝ × M ↦ (F.connection (T - z.1 ^ 2)).scalarCurvature z.2) (s, α s) :=
    ((squareTime_scalar_smooth F hM04 T τmax hτmax hwindow).contMDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨htime, Set.mem_univ (α s)⟩)).mdifferentiableAt
      (by simp)
  have hchain := hasDerivAt_parametric_curve
    (fun z : ℝ × M ↦ (F.connection (T - z.1 ^ 2)).scalarCurvature z.2) α s hf hα
  have hsquare : s ^ 2 ∈ Set.Icc 0 b := by
    constructor
    · exact sq_nonneg s
    · nlinarith [hs.1, hs.2, Real.sqrt_nonneg b, Real.sq_sqrt hb.le]
  have hnear : ∀ᶠ r in 𝓝 s, r ^ 2 ∈ Set.Icc 0 b := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact ⟨sq_nonneg r, by nlinarith [hr.1, hr.2, Real.sqrt_nonneg b, Real.sq_sqrt hb.le]⟩
  have hsqd : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hpartial := (backward_scalar_hasDerivWithinAt (F := F) hM04 hwindow hmax.le
    hsquare (α s)).comp_hasDerivAt (h := fun r : ℝ ↦ r ^ 2) s hsqd hnear
  dsimp only [Function.comp_def] at hpartial hchain
  rw [hpartial.deriv] at hchain
  convert! hchain using 1 <;> ring

end PoincareConjecture.Proofs.M09
