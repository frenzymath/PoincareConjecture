import PoincareConjecture.Proofs.M30.Thm11_1.StationaryCompleteness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M30

theorem metricComplete_flowout_pullback
    {n : ℕ} {S : Type u} {N : Type v}
    [TopologicalSpace S] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) N]
    [IsManifold (𝓡 n) ∞ S] [IsManifold (𝓡 (n + 1)) ∞ N]
    [T3Space S] [CompactSpace S]
    (g : RiemannianMetric (n + 1) N) (Phi : ℝ → N → N) (j : S → N)
    (hPhi : ∀ t : ℝ, ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (Phi t))
    (hact : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (hmetric : ∀ (t : ℝ) (x : N) (a b : TangentSpace (𝓡 (n + 1)) x),
      g.inner (Phi t x) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Phi t) x a)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Phi t) x b) = g.inner x a b) :
    letI := RiemannianMetric.lineProductChartedSpace (n := n) (M := S)
    letI := RiemannianMetric.lineProductIsManifold (n := n) (M := S)
    let Xi : S × ℝ → N := fun z => Phi z.2 (j z.1)
    ∀ hXi : IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ Xi,
      MetricComplete (g.pullbackOfLocalDiffeomorph Xi hXi) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (S × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) S ℝ ℝ
  let := RiemannianMetric.lineProductChartedSpace (n := n) (M := S)
  let := RiemannianMetric.lineProductIsManifold (n := n) (M := S)
  dsimp only
  intro hXi
  let Xi : S × ℝ → N := fun z => Phi z.2 (j z.1)
  let G := g.pullbackOfLocalDiffeomorph Xi hXi
  let e : (S × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ (S × ℝ) := by
    refine { toEquiv := Equiv.refl _
             contMDiff_toFun := ?_
             contMDiff_invFun := ?_ }
    · change ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞ (id : S × ℝ → _)
      rw [← modelWithCornersSelf_prod]
      exact Poincare.Manifold.contMDiff_linearRechart_id (M := S × ℝ)
        (RiemannianMetric.lineModelEquiv n)
    · change ContMDiff (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (id : S × ℝ → _)
      rw [← modelWithCornersSelf_prod]
      exact Poincare.Manifold.contMDiff_linearRechart_id_symm (M := S × ℝ)
        (RiemannianMetric.lineModelEquiv n)
  have hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ (Prod.snd : S × ℝ → ℝ) := by
    have hs : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (Prod.snd : S × ℝ → ℝ) := contMDiff_snd
    exact hs.comp e.symm.contMDiff
  let Psi (t : ℝ) (z : S × ℝ) : S × ℝ := (z.1, z.2 + t)
  have hPsi (t : ℝ) : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (Psi t) := by
    have hs : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : S × ℝ => (z.1, z.2 + t)) :=
      contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)
    exact e.contMDiff.comp (hs.comp e.symm.contMDiff)
  have hequiv (t : ℝ) : Xi ∘ Psi t = Phi t ∘ Xi := by
    funext z
    change Phi (z.2 + t) (j z.1) = Phi t (Phi z.2 (j z.1))
    rw [add_comm z.2 t, hact]
  have hinner (t : ℝ) (z : S × ℝ) (a b : TangentSpace (𝓡 (n + 1)) z) :
      G.inner (Psi t z) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Psi t) z a)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Psi t) z b) = G.inner z a b := by
    have hderiv :
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) Xi (Psi t z)).comp
            (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Psi t) z) =
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Phi t) (Xi z)).comp
            (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) Xi z) := by
      rw [← mfderiv_comp z (hXi.contMDiff.mdifferentiable (by simp) (Psi t z))
        ((hPsi t).mdifferentiable (by simp) z), hequiv t,
        mfderiv_comp z ((hPhi t).mdifferentiable (by simp) (Xi z))
          (hXi.contMDiff.mdifferentiable (by simp) z)]
    have ha := congrArg (fun L => L a) hderiv
    have hb := congrArg (fun L => L b) hderiv
    have hpoint : Xi (Psi t z) = Phi t (Xi z) := congrFun (hequiv t) z
    dsimp only [ContinuousLinearMap.comp_apply] at ha hb
    dsimp only [G]
    rw [RiemannianMetric.pullbackOfLocalDiffeomorph_inner,
      RiemannianMetric.pullbackOfLocalDiffeomorph_inner, ha, hb, hpoint]
    exact hmetric t (Xi z) _ _
  apply metricComplete_of_proper_height_and_metric_translations G hf
    isProperMap_snd_of_compactSpace
    (isCompact_univ.prod (show IsCompact ({0} : Set ℝ) from isCompact_singleton))
    (fun t => (hPsi t).mdifferentiable (by simp)) hinner (fun _ _ => rfl)
  intro z
  refine ⟨-z.2, ?_⟩
  simp [Psi]

end PoincareConjecture.M30
