import PoincareConjecture.Proofs.M64.Mathlib.ImmersionMetric





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m64_induced_metrics_comp_germ
    (g : RiemannianMetric n M)
    (h H : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2)))
    {F f : EuclideanSpace ℝ (Fin 2) → M}
    {k : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {p : EuclideanSpace ℝ (Fin 2)}
    (hk : ContDiffAt ℝ 1 k p)
    (hf : ∀ᶠ q in 𝓝 (k p), MDifferentiableAt (𝓡 2) (𝓡 n) f q)
    (hcomp : F =ᶠ[𝓝 p] f ∘ k)
    (hFmetric : ∀ᶠ q in 𝓝 p, ∀ u v : EuclideanSpace ℝ (Fin 2),
      h.inner q u v = g.inner (F q) (mfderiv (𝓡 2) (𝓡 n) F q u)
        (mfderiv (𝓡 2) (𝓡 n) F q v))
    (hfmetric : ∀ᶠ q in 𝓝 (k p), ∀ u v : EuclideanSpace ℝ (Fin 2),
      H.inner q u v = g.inner (f q) (mfderiv (𝓡 2) (𝓡 n) f q u)
        (mfderiv (𝓡 2) (𝓡 n) f q v)) :
    ∀ᶠ q in 𝓝 p, ∀ u v : EuclideanSpace ℝ (Fin 2), h.inner q u v =
      H.inner (k q) (fderiv ℝ k q u) (fderiv ℝ k q v) := by
  filter_upwards [hFmetric, hk.continuousAt.eventually hfmetric,
    hk.continuousAt.eventually hf, hk.eventually (by simp), hcomp.eventually_nhds]
    with q hFq hfq hdfq hdkq hq u v
  change F =ᶠ[𝓝 q] f ∘ k at hq
  have hdk : MDifferentiableAt (𝓡 2) (𝓡 2) k q :=
    mdifferentiableAt_iff_differentiableAt.mpr (hdkq.differentiableAt (by simp))
  have hd := hq.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 n)
  rw [mfderiv_comp q hdfq hdk] at hd
  have hdv (w : EuclideanSpace ℝ (Fin 2)) :
      mfderiv (𝓡 2) (𝓡 n) F q w =
        mfderiv (𝓡 2) (𝓡 n) f (k q) (fderiv ℝ k q w) := by
    have he := congrArg (fun L => L w) hd
    simp only [mfderiv_eq_fderiv] at he
    convert! he using 1
  have hpoint : F q = f (k q) := hq.self_of_nhds
  rw [hFq, hfq, hpoint]
  exact congrArg₂ (fun a b : EuclideanSpace ℝ (Fin n) => g.inner (f (k q)) a b)
    (hdv u) (hdv v)

end PoincareConjecture
