import PoincareConjecture.Proofs.M03.Existence.PullbackMetricNative
import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "FiberBilin" =>
  fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

structure PullbackMetricFamilyData (J : Set ℝ) (g₀ : RiemannianMetric n M) where
  baseMetric : ℝ → RiemannianMetric n M
  diffeo : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞
  sliceSmooth : ∀ t : ℝ,
    ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x
        (pinner (baseMetric t) (diffeo t) x))
  jointSmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, pinner (baseMetric p.1) (diffeo p.1) p.2⟩ :
          Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) FiberBilin))
      (J ×ˢ Set.univ)
  baseInitial : baseMetric 0 = g₀
  diffeoInitial : diffeo 0 = Diffeomorph.refl (𝓡 n) M ∞

namespace PullbackMetricFamilyData

variable {J : Set ℝ} {g₀ : RiemannianMetric n M}
  (P : PullbackMetricFamilyData (n := n) (M := M) J g₀)

noncomputable def metric (t : ℝ) : RiemannianMetric n M :=
  pullbackMetric (P.baseMetric t) (P.diffeo t) (P.sliceSmooth t)

theorem metric_inner (t : ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (P.metric t).inner x v w =
      (P.baseMetric t).inner (P.diffeo t x)
        (mfderiv (𝓡 n) (𝓡 n) (P.diffeo t) x v)
        (mfderiv (𝓡 n) (𝓡 n) (P.diffeo t) x w) := by
  exact pullbackMetric_inner (g := P.baseMetric t) (Φ := P.diffeo t)
    (hsmooth := P.sliceSmooth t) x v w

theorem metric_initial : P.metric 0 = g₀ := by
  let hs0 := P.sliceSmooth 0
  have h := pullbackMetric_refl g₀
    (by simpa [P.baseInitial, P.diffeoInitial] using hs0)
  simpa [metric, P.baseInitial, P.diffeoInitial] using h

theorem metric_isSmoothFamilyOn :
    RiemannianMetric.IsSmoothFamilyOn P.metric J := by
  exact P.jointSmooth

end PullbackMetricFamilyData

end PoincareConjecture
