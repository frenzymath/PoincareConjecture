import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing



theorem axial_deriv_ne_zero_of_mfderiv_injective (F : RoundCylinderSpace → RoundCylinderSpace)
    (hF : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ F)
    (hfst : ∀ p, (F p).1 = p.1) (p : RoundCylinderSpace)
    (hinj : Function.Injective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) F p)) :
    deriv (fun t => (F (p.1, t)).2) p.2 ≠ 0 := by
  intro hzero
  have hpair : F = fun z => (z.1, (F z).2) :=
    funext (fun z => Prod.ext (hfst z) rfl)
  have hv : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) F p
      (0, 1) = 0 := by
    have hd := mfderiv_prodMk (x := p) mdifferentiableAt_fst
      ((contMDiff_snd.comp hF).mdifferentiableAt (by simp))
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z => (z.1, (F z).2)) p = _ at hd
    rw [hpair, hd]
    apply Prod.ext
    · change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 2) Prod.fst p (0, 1) = 0
      rw [mfderiv_fst]
      rfl
    · change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun z => (F z).2) p (0, 1) = 0
      have hdpartial := mfderiv_prod_eq_add_apply
        (p := p) (v := ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)))
        ((contMDiff_snd.comp hF).mdifferentiableAt (by simp))
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun z => (F z).2) p (0, 1) = _ at hdpartial
      rw [hdpartial]
      simp only [map_zero, zero_add]
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun t => (F (p.1, t)).2) p.2 (1 : ℝ) = 0
      rw [fderiv_apply_one_eq_deriv, hzero]
  have hvzero : ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) = (0, (0 : ℝ)) :=
    hinj (hv.trans (map_zero _).symm)
  exact one_ne_zero (congrArg Prod.snd hvzero)



theorem vertical_mfderiv_bijective (h : RoundCylinderSpace → ℝ)
    (hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h)
    (p : RoundCylinderSpace) {a : ℝ} (ha : a ≠ 0)
    (hderiv : HasDerivAt (fun t => h (p.1, t)) a p.2) :
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) p) := by
  let D : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] ℝ :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) h p
  let Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q => h (q, p.2)) p.1
  have hvertical (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
      D v = Q v.1 + a * v.2 := by
    dsimp only [D, Q]
    erw [mfderiv_prod_eq_add_apply (hh.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, fderiv_eq_deriv_mul (𝕜 := ℝ), hderiv.deriv]
    rfl
  have htotal : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z => (z.1, h z)) p =
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).prod D := by
    rw [mfderiv_prodMk mdifferentiableAt_fst (hh.mdifferentiableAt (by simp)),
      mfderiv_fst]
    rfl
  have hinj : Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) p) := by
    intro v w hvw
    rw [htotal] at hvw
    have hfirst := congrArg Prod.fst hvw
    change v.1 = w.1 at hfirst
    have hsecond : D v = D w := congrArg Prod.snd hvw
    rw [hvertical, hvertical, hfirst] at hsecond
    exact Prod.ext hfirst (mul_left_cancel₀ ha (add_left_cancel hsecond))
  let L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z : RoundCylinderSpace => (z.1, h z)) p
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩



theorem exists_vertical_diffeomorph (h : RoundCylinderSpace → ℝ)
    (hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h)
    (hbij : ∀ q : UnitTwoSphere, Function.Bijective (fun t => h (q, t)))
    (hderiv : ∀ p : RoundCylinderSpace, ∃ a : ℝ, a ≠ 0 ∧
      HasDerivAt (fun t => h (p.1, t)) a p.2) :
    ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        RoundCylinderSpace RoundCylinderSpace ∞,
      ∀ p, D p = (p.1, h p) := by
  classical
  let F : RoundCylinderSpace → RoundCylinderSpace := fun p => (p.1, h p)
  have hFbij : Function.Bijective F := by
    constructor
    · rintro ⟨q, s⟩ ⟨z, t⟩ heq
      have hq : q = z := congrArg Prod.fst heq
      subst z
      exact Prod.ext rfl ((hbij q).1 (congrArg Prod.snd heq))
    · rintro ⟨q, s⟩
      obtain ⟨t, ht⟩ := (hbij q).2 s
      exact ⟨(q, t), Prod.ext rfl ht⟩
  let e := Equiv.ofBijective F hFbij
  have hF : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ F :=
    contMDiff_fst.prodMk hh
  have hi : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm := by
    intro y
    obtain ⟨p, rfl⟩ := e.surjective y
    obtain ⟨a, ha, hd⟩ := hderiv p
    let : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) RoundCylinderSpace :=
      prodChartedSpace _ _ _ _
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ RoundCylinderSpace := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) UnitTwoSphere ℝ
    have hf' := hF.contMDiffAt (x := p)
    have hd' := vertical_mfderiv_bijective h hh p ha hd
    rw [← modelWithCornersSelf_prod] at hf' hd' ⊢
    exact Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces
      hf' hd' (Filter.Eventually.of_forall e.symm_apply_apply)
  exact ⟨{ e with contMDiff_toFun := hF, contMDiff_invFun := hi }, fun _ => rfl⟩

end PoincareConjecture.CylinderGluing
