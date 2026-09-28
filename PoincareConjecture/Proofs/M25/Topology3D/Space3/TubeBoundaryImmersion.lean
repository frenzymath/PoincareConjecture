import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceSurfacePullback












set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem tube_boundary_smooth_immersion (e : OpenPartialHomeomorph (E2 × ℝ) E3)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {J : Set ℝ} (hs : sphere 0 1 ×ˢ J ⊆ e.source) :
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
        (fun p : UnitCircle × ℝ => e (p.1.1, p.2)) (univ ×ˢ J) ∧
      InjOn (fun p : UnitCircle × ℝ => e (p.1.1, p.2)) (univ ×ˢ J) ∧
      ∀ p ∈ (univ : Set UnitCircle) ×ˢ J, Injective
        (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3)
          (fun p : UnitCircle × ℝ => e (p.1.1, p.2)) p) := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let i : UnitCircle × ℝ → E2 × ℝ := Prod.map Subtype.val id
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ ((↑) : UnitCircle → E2) :=
    contMDiff_coe_sphere
  have hidR : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (id : ℝ → ℝ) := contMDiff_id
  have him : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ) ∞ i := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcoe.prodMap hidR
  have hiU : MapsTo i (univ ×ˢ J) e.source := fun p hp => hs ⟨p.1.2, hp.2⟩
  have hem : e.MDifferentiable 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) :=
    ⟨he.contMDiffOn.mdifferentiableOn (by simp),
      hei.contMDiffOn.mdifferentiableOn (by simp)⟩
  refine ⟨he.contMDiffOn.comp him.contMDiffOn hiU, ?_, ?_⟩
  · intro p hp q hq hpq
    have h := e.injOn (hiU hp) (hiU hq) hpq
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    exact Prod.ext (Subtype.ext hfst) hsnd
  · intro p hp
    have hid : Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ) i p) := by
      change Injective
        (fun w => mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ)
          (Prod.map ((↑) : UnitCircle → E2) (id : ℝ → ℝ)) p w)
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      have hprod := mfderiv_prodMap
        (I := 𝓡 1) (I' := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, E2)) (J' := 𝓘(ℝ, ℝ))
        (f := ((↑) : UnitCircle → E2)) (g := (id : ℝ → ℝ)) (p := p)
        (hcoe.mdifferentiable (by simp) p.1) (hidR.mdifferentiable (by simp) p.2)
      rw [hprod, mfderiv_id]
      intro a b hab
      have hfst := congrArg Prod.fst hab
      have hsnd := congrArg Prod.snd hab
      exact Prod.ext (injective_mvfderiv_subtypeVal_sphere p.1 hfst) hsnd
    change Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) (e ∘ i) p)
    rw [mfderiv_comp p (hem.mdifferentiableAt (hiU hp))
      (him.mdifferentiable (by simp) p)]
    exact (hem.mfderiv_injective (hiU hp)).comp hid

end PoincareConjecture.M25.Topology3D
