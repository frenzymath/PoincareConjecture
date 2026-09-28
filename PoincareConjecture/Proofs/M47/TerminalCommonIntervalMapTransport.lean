import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCrossTail
import PoincareConjecture.Proofs.M47.TerminalGermsUniverseMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

theorem terminalCommonInterval_control_reindex
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : ℕ → Type w} [∀ n, TopologicalSpace (X n)]
    [∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 M) (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, OpenPartialHomeomorph M (X n))
    (hc : terminalCommonInterval_compactTangentControl g h e)
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop) :
    terminalCommonInterval_compactTangentControl g (fun n => h (sigma n))
      (fun n => e (sigma n)) := by
  intro K hK lambda hlambda hlambda_lt
  exact hsigma.eventually (hc K hK lambda hlambda hlambda_lt)

theorem terminalCommonInterval_control_diffeomorph
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    {X : ℕ → Type w} [∀ n, TopologicalSpace (X n)]
    [∀ n, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X n)]
    [∀ n, IsManifold (𝓡 3) ∞ (X n)]
    (g : RiemannianMetric 3 N) (h : ∀ n, RiemannianMetric 3 (X n))
    (e : ∀ n, OpenPartialHomeomorph N (X n))
    (he : ∀ n, ContMDiffOn (𝓡 3) (𝓡 3) 1 (e n) (e n).source)
    (hc : terminalCommonInterval_compactTangentControl g h e)
    (d : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    terminalCommonInterval_compactTangentControl
      (g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph) h
      (fun n => d.toHomeomorph.toOpenPartialHomeomorph.trans (e n)) := by
  intro K hK lambda hlambda hlambda_lt
  filter_upwards [hc (d '' K) (hK.image d.continuous) lambda hlambda hlambda_lt] with n hn
  refine ⟨fun x hx => ⟨mem_univ _, hn.1 (mem_image_of_mem d hx)⟩, ?_⟩
  intro x hx v
  have hdx := hn.1 (mem_image_of_mem d hx)
  have hed := ((he n (d x) hdx).contMDiffAt
    ((e n).open_source.mem_nhds hdx)).mdifferentiableAt (by simp)
  have hb := hn.2 (d x) (mem_image_of_mem d hx) (mfderiv (𝓡 3) (𝓡 3) d x v)
  change lambda * (g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph).tangentNorm x v ≤
      (h n).tangentNorm (e n (d x)) (mfderiv (𝓡 3) (𝓡 3) ((e n) ∘ d) x v) ∧
    (h n).tangentNorm (e n (d x)) (mfderiv (𝓡 3) (𝓡 3) ((e n) ∘ d) x v) ≤
      lambda⁻¹ * (g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph).tangentNorm x v
  rw [mfderiv_comp x hed (d.mdifferentiable (by simp) x)]
  exact hb

end PoincareConjecture.M47
