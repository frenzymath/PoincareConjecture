import PoincareConjecture.Proofs.M03.Existence.PullbackMetricNative
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem hasDerivWithinAt_pullbackMetric_of_jointFDeriv
    (g : ℝ → RiemannianMetric n M)
    (Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hsmooth : ∀ s : ℝ,
      ContMDiff (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun y : M => Bundle.TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) y
          (pinner (g s) (Φ s) y)))
    {J : Set ℝ} {t : ℝ} {x : M}
    {u v : TangentSpace (𝓡 n) x}
    {L : (ℝ × ℝ) →L[ℝ] ℝ}
    (hF : HasFDerivWithinAt
      (fun q : ℝ × ℝ =>
        (g q.1).inner (Φ q.2 x)
          (mfderiv (𝓡 n) (𝓡 n) (Φ q.2) x u)
          (mfderiv (𝓡 n) (𝓡 n) (Φ q.2) x v))
      L (J ×ˢ J) (t, t)) :
    HasDerivWithinAt
      (fun s : ℝ =>
        (pullbackMetric (g s) (Φ s) (hsmooth s)).inner x u v)
      (L (1, 1)) J t := by
  let diag : ℝ → ℝ × ℝ := fun s => (s, s)
  have hdiag : HasDerivWithinAt diag (1, 1) J t := by
    simpa only [diag, id_eq] using
      (hasDerivWithinAt_id t J).prodMk (hasDerivWithinAt_id t J)
  have hmaps : Set.MapsTo diag J (J ×ˢ J) := by
    intro s hs
    exact ⟨hs, hs⟩
  have hF' : HasFDerivWithinAt
      (fun q : ℝ × ℝ =>
        (g q.1).inner (Φ q.2 x)
          (mfderiv (𝓡 n) (𝓡 n) (Φ q.2) x u)
          (mfderiv (𝓡 n) (𝓡 n) (Φ q.2) x v))
      L (J ×ˢ J) (diag t) := by
    simpa [diag] using hF
  have hcomp := HasFDerivWithinAt.comp_hasDerivWithinAt t hF' hdiag hmaps
  apply hcomp.congr
  · intro s hs
    rw [pullbackMetric_inner]
    rfl
  · rw [pullbackMetric_inner]
    rfl

end PoincareConjecture
