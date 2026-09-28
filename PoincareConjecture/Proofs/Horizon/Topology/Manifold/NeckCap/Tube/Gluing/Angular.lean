import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.CylinderGluing

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem exists_fiber_diffeomorph
    (f : ℝ → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (hf : ContMDiff CylModel (𝓡 2) ∞
      (fun p : RoundCylinderSpace => f p.2 p.1)) :
    ∃ D : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
      ∀ p : RoundCylinderSpace, D p = (f p.2 p.1, p.2) := by
  let F : RoundCylinderSpace → RoundCylinderSpace := fun p => (f p.2 p.1, p.2)
  let G : RoundCylinderSpace → RoundCylinderSpace := fun p => ((f p.2).symm p.1, p.2)
  have hF : ContMDiff CylModel CylModel ∞ F := hf.prodMk contMDiff_snd
  have hleft : Function.LeftInverse G F := by
    rintro ⟨q, t⟩
    exact Prod.ext ((f t).symm_apply_apply q) rfl
  have hright : Function.RightInverse G F := by
    rintro ⟨q, t⟩
    exact Prod.ext ((f t).apply_symm_apply q) rfl
  have hd (p : RoundCylinderSpace) : Function.Bijective (mfderiv CylModel CylModel F p) := by
    let L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) × ℝ) := mfderiv CylModel CylModel F p
    have hi : Function.Injective L := by
      intro v w hvw
      have htotal : L =
          (mfderiv CylModel (𝓡 2)
            (fun z : RoundCylinderSpace => f z.2 z.1) p).prod
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) := by
        dsimp [L, F]
        rw [mfderiv_prodMk (hf.mdifferentiableAt (by simp)) mdifferentiableAt_snd,
          mfderiv_snd]
        rfl
      rw [htotal] at hvw
      have hvw2 := congrArg Prod.snd hvw
      change v.2 = w.2 at hvw2
      have hvw1 := congrArg Prod.fst hvw
      change mfderiv CylModel (𝓡 2)
          (fun z : RoundCylinderSpace => f z.2 z.1) p v =
        mfderiv CylModel (𝓡 2)
          (fun z : RoundCylinderSpace => f z.2 z.1) p w at hvw1
      rw [mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp)),
        mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp)), hvw2] at hvw1
      apply Prod.ext _ hvw2
      exact ((f p.2).mfderivToContinuousLinearEquiv (by simp) p.1).injective
        (add_right_cancel hvw1)
    exact ⟨hi, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hi⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) RoundCylinderSpace :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ RoundCylinderSpace := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) UnitTwoSphere ℝ
  have hG : ContMDiff CylModel CylModel ∞ G := by
    intro p
    have h : ContMDiffAt CylModel CylModel ∞ G (F (G p)) := by
      have hf' := hF.contMDiffAt (x := G p)
      have hd' := hd (G p)
      rw [← modelWithCornersSelf_prod] at hf' hd' ⊢
      exact Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces
        hf' hd' (Eventually.of_forall hleft)
    rw [hright p] at h
    exact h
  exact ⟨{ toEquiv := ⟨F, G, hleft, hright⟩
           contMDiff_toFun := hF
           contMDiff_invFun := hG }, fun _ => rfl⟩

end PoincareConjecture.CylinderGluing
