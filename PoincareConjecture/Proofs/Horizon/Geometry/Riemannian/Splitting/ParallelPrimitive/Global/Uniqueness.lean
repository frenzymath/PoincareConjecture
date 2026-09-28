import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Constancy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ParallelPrimitive

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem eqOn_of_mvfderiv_eq (U : Opens M) (hUc : IsPreconnected (U : Set M))
    {f k : M → ℝ} (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hk : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ k U)
    (hd : ∀ x ∈ U, mvfderiv (𝓡 n) f x = mvfderiv (𝓡 n) k x)
    {p : M} (hp : p ∈ U) (he : f p = k p) : EqOn f k U := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x : U => f x - k x) := by
    intro x
    exact contMDiffAt_subtype_iff.mpr
      ((hf.contMDiffAt (U.isOpen.mem_nhds x.property)).sub
        (hk.contMDiffAt (U.isOpen.mem_nhds x.property)))
  have hz (x : U) (v : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) (fun x : U => f x - k x) x v = 0 := by
    have hf' := (hf.contMDiffAt (U.isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
    have hk' := (hk.contMDiffAt (U.isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
    change mvfderiv (𝓡 n) ((f - k) ∘ (Subtype.val : U → M)) x v = 0
    rw [mvfderiv_comp_apply x (hf'.sub hk')
      ((contMDiff_subtype_val (I := 𝓡 n) (n := ∞)).mdifferentiable (by simp) x) v,
      mvfderiv_sub hf' hk', hd x x.property, sub_self, zero_apply]
  intro x hx
  have h := Poincare.Manifold.eq_of_mvfderiv_eq_zero
    (hs.mdifferentiable (by simp)) hz (⟨x, hx⟩ : U) ⟨p, hp⟩
  change f x - k x = f p - k p at h
  rw [he, sub_self] at h
  exact sub_eq_zero.mp h

end PoincareConjecture.ParallelPrimitive
