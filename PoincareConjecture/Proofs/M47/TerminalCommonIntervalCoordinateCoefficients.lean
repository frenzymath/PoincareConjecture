import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSmoothLimit
import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialChartMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCommonInterval_coordinate_coefficients_smooth
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {X : ℕ → Type v} [∀ n, TopologicalSpace (X n)] [∀ n, ChartedSpace E (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X n) ∞)
    (hsource : ∀ K : Set M, IsCompact K → ∀ᶠ n in atTop, K ⊆ (e n).source)
    (a : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞) :
    LocallyEventuallyContDiff a.target
      (fun n => (h n).pullbackCoefficients (e n ∘ a.symm)) := by
  intro K hK hKa
  have himage : IsCompact (a.symm '' K) := hK.image_of_continuousOn
    (a.toOpenPartialHomeomorph.continuousOn_invFun.mono hKa)
  filter_upwards [hsource _ himage] with n hn
  let T := a.symm.trans (e n)
  refine ⟨T.source, T.open_source, ?_, ?_⟩
  · intro x hx
    exact ⟨hKa hx, hn (mem_image_of_mem a.symm hx)⟩
  · intro x hx
    exact ((h n).contDiffAt_pullbackCoefficients
      (T.contMDiffOn_toFun.contMDiffAt (T.open_source.mem_nhds hx))).contDiffWithinAt

theorem terminalCommonInterval_coordinate_coefficients_symmetric
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : E → M) (x v w : E) :
    g.pullbackCoefficients f x v w = g.pullbackCoefficients f x w v := by
  exact g.symm _ _ _

theorem terminalCommonInterval_coordinate_limit_coefficients
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M)
    (a : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞) :
    ContDiffOn ℝ ∞ (g.pullbackCoefficients a.symm) a.target ∧
      ∀ x ∈ a.target, ∀ v : E, v ≠ 0 → 0 < g.pullbackCoefficients a.symm x v v := by
  refine ⟨(terminalCurvature_partial_chart_coefficients g a).1, ?_⟩
  intro x hx v hv
  have hlocal := a.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) a.symm x) :=
    (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  apply g.pos
  intro hz
  apply hv
  apply hinj
  rw [map_zero]
  convert! hz using 1

end PoincareConjecture.M47
