import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceTubeChart

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem source_collar_slice_smooth_immersion
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    (t : ℝ) (ht : ∀ θ : UnitCircle, (θ, t) ∈ Q.source) :
    ContMDiff (𝓡 1) (𝓡 2) ∞ (fun θ : UnitCircle => Q (θ, t)) ∧
      Injective (fun θ : UnitCircle => Q (θ, t)) ∧
      ∀ θ, Injective (mfderiv (𝓡 1) (𝓡 2) (fun θ : UnitCircle => Q (θ, t)) θ) := by
  let i : UnitCircle → UnitCircle × ℝ := fun θ => (θ, t)
  have him : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ i :=
    contMDiff_id.prodMk contMDiff_const
  have hem : Q.MDifferentiable ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) :=
    ⟨hQ.mdifferentiableOn (by simp), hQi.mdifferentiableOn (by simp)⟩
  refine ⟨contMDiffOn_univ.mp (hQ.comp him.contMDiffOn (fun θ _ => ht θ)), ?_, ?_⟩
  · intro θ η hθη
    exact congrArg Prod.fst (Q.injOn (ht θ) (ht η) hθη)
  · intro θ
    have hid : Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℝ)) i θ) := by
      change Injective (mfderiv (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, ℝ))
        (fun p : UnitCircle => (p, t)) θ)
      rw [mfderiv_prod_left]
      exact fun _ _ h => congrArg Prod.fst h
    change Injective (mfderiv (𝓡 1) (𝓡 2) (Q ∘ i) θ)
    rw [mfderiv_comp θ (hem.mdifferentiableAt (ht θ))
      (him.mdifferentiable (by simp) θ)]
    exact (hem.mfderiv_injective (ht θ)).comp hid

end PoincareConjecture.M25.Topology3D
