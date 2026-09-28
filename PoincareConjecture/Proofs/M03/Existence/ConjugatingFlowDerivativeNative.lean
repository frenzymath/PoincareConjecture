import PoincareConjecture.Proofs.M03.Existence.PullbackMetricDerivativeNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckGaugeSign











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem hasDerivWithinAt_pullbackMetric_add_negW
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
      L (J ×ˢ J) (t, t))
    {c : ℝ → ℝ}
    (hc : HasDerivWithinAt c (-L (1, 1)) J t) :
    HasDerivWithinAt
      (fun s : ℝ =>
        (pullbackMetric (g s) (Φ s) (hsmooth s)).inner x u v + c s)
      0 J t := by
  have hpull := hasDerivWithinAt_pullbackMetric_of_jointFDeriv
    (g := g) (Φ := Φ) hsmooth hF
  have hpull' : HasDerivWithinAt
      (fun s : ℝ =>
        (pullbackMetric (g s) (Φ s) (hsmooth s)).inner x u v)
      (0 + L (1, 1)) J t := by
    simpa using hpull
  exact DeTurckNative.hasDerivWithinAt_pullback_source_cancel
    (A := 0) (L := L (1, 1)) hpull' hc

end PoincareConjecture

end
