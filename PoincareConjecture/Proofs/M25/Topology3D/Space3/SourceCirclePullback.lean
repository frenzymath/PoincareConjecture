import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight













set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_collar_circle_source_pullback
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (c : UnitCircle → E3) (hc : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ c)
    (hci : Injective c)
    (hcd : ∀ θ, Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) c θ))
    (hcentral : range c ⊆ range (fun p : UnitTwoSphere => ψ (p, 0))) :
    ∃ q : UnitCircle → UnitTwoSphere,
      ContMDiff (𝓡 1) (𝓡 2) ∞ q ∧ Injective q ∧
      (∀ θ, Injective (mfderiv (𝓡 1) (𝓡 2) q θ)) ∧
      ∀ θ, ψ (q θ, 0) = c θ := by
  obtain ⟨ec, hec, hsource, htarget, heci⟩ := exists_collar_chart ψ hψ
  let q : UnitCircle → UnitTwoSphere := fun θ => (ec.symm (c θ)).1
  have hsource0 (p : UnitTwoSphere) : (p, (0 : ℝ)) ∈ ec.source := by
    rw [hsource]
    exact ⟨mem_univ _, by norm_num⟩
  have hcU (θ : UnitCircle) : c θ ∈ ec.target := by
    rw [htarget]
    obtain ⟨p, hp⟩ := hcentral ⟨θ, rfl⟩
    exact ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, hp⟩
  have hq : ContMDiff (𝓡 1) (𝓡 2) ∞ q := by
    apply contMDiffOn_univ.mp
    have hi : ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞
        (fun y => (ec.symm y).1) ec.target :=
      contMDiff_fst.comp_contMDiffOn heci
    exact hi.comp hc.contMDiffOn (fun θ _ => hcU θ)
  have hrec : (fun p : UnitTwoSphere => ψ (p, 0)) ∘ q = c := by
    funext θ
    obtain ⟨p, hp⟩ := hcentral ⟨θ, rfl⟩
    have hinv : ec.symm (c θ) = (p, 0) := by
      calc
        ec.symm (c θ) = ec.symm (ec (p, 0)) :=
          congrArg ec.symm ((congrFun hec (p, 0)).trans hp).symm
        _ = (p, 0) := ec.left_inv (hsource0 p)
    change ψ ((ec.symm (c θ)).1, 0) = c θ
    rw [hinv]
    exact hp
  refine ⟨q, hq, ?_, ?_, fun θ => congrFun hrec θ⟩
  · intro θ η hθη
    apply hci
    rw [← congrFun hrec θ, ← congrFun hrec η]
    exact congrArg (fun p : UnitTwoSphere => ψ (p, 0)) hθη
  · intro θ
    have hd := ((collar_central_contMDiff ψ hψ).mdifferentiable
      (by simp) (q θ)).hasMFDerivAt.comp θ
        (hq.mdifferentiable (by simp) θ).hasMFDerivAt
    rw [hrec] at hd
    intro a b hab
    apply hcd θ
    rw [hd.mfderiv]
    exact congrArg
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun p : UnitTwoSphere => ψ (p, 0)) (q θ)) hab




theorem exists_pole_off_regular_height (h : UnitTwoSphere → ℝ) (t : ℝ)
    (p : UnitTwoSphere) (hreg : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) h p ≠ 0) :
    ∃ v : UnitTwoSphere, h v ≠ t := by
  classical
  by_contra hnone
  have hconst : h = fun _ => t := by
    funext v
    by_contra hv
    exact hnone ⟨v, hv⟩
  apply hreg
  rw [hconst, mfderiv_const]

end PoincareConjecture.M25.Topology3D
