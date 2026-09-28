import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩



theorem exists_planar_boundary_reparametrization
    (γ : S1 -> E2) (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ)
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hboundary : A '' sphere (0 : E2) 1 = range γ) :
    ∃ q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞,
      ∀ p : S1, A (q p : E2) = γ p := by
  have hmem (p : S1) : A.symm (γ p) ∈ sphere (0 : E2) 1 := by
    obtain ⟨x, hx, hxp⟩ := hboundary.symm ▸ mem_range_self p
    rw [← hxp, A.symm_apply_apply]
    exact hx
  let Q : S1 -> S1 := fun p => ⟨A.symm (γ p), hmem p⟩
  have hQ (p : S1) : A (Q p : E2) = γ p := A.apply_symm_apply (γ p)
  have hQs : ContMDiff (𝓡 1) (𝓡 1) ∞ Q :=
    (A.symm.contMDiff.comp hγ.contMDiff).codRestrict_sphere hmem
  have hQbij : Bijective Q := by
    constructor
    · intro p q hpq
      apply hγ.isEmbedding.injective
      rw [← hQ p, ← hQ q, hpq]
    · intro p
      obtain ⟨q, hq⟩ := hboundary ▸ mem_image_of_mem A p.property
      refine ⟨q, ?_⟩
      apply Subtype.ext
      change A.symm (γ q) = (p : E2)
      rw [hq, A.symm_apply_apply]
  let B : S1 -> E2 := fun p => A p
  have hB : ContMDiff (𝓡 1) (𝓡 2) ∞ B := A.contMDiff.comp contMDiff_coe_sphere
  have hfactor : γ = B ∘ Q := funext fun p => (hQ p).symm
  have hQderiv (p : S1) : Bijective (mfderiv (𝓡 1) (𝓡 1) Q p) := by
    have hγinj : Injective (mfderiv (𝓡 1) (𝓡 2) γ p) :=
      (hγ.isImmersion.isImmersionAt p).injective_mfderiv_modelWithCornersSelf (by simp)
    have hchain := mfderiv_comp p ((hB (Q p)).mdifferentiableAt (by simp))
      ((hQs p).mdifferentiableAt (by simp))
    rw [← hfactor] at hchain
    have hinj : Injective (mfderiv (𝓡 1) (𝓡 1) Q p) := by
      intro u v huv
      apply hγinj
      rw [hchain]
      exact congrArg (mfderiv (𝓡 1) (𝓡 2) B (Q p)) huv
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E1) (V₂ := E1)
      (f := (mfderiv (𝓡 1) (𝓡 1) Q p).toLinearMap) rfl).mp hinj⟩
  let hlocal := Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hQs hQderiv
  let q := hlocal.diffeomorphOfBijective hQbij
  exact ⟨q, hQ⟩

end Poincare.Manifold.Schoenflies
