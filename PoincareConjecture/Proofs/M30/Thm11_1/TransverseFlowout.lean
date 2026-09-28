import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M30



theorem isLocalDiffeomorph_transverseFlowout
    {n : ℕ} {S : Type u} {Q : Type v}
    [TopologicalSpace S] [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Q]
    [IsManifold (𝓡 n) ∞ S] [IsManifold (𝓡 (n + 1)) ∞ Q]
    {j : S → Q} {X : (x : Q) → TangentSpace (𝓡 (n + 1)) x}
    {Phi : ℝ → Q → Q}
    (hj : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ j)
    (hj_inj : ∀ q, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) j q))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞
      (Function.uncurry Phi))
    (hcurve : ∀ x, IsMIntegralCurve (I := 𝓡 (n + 1)) (fun t => Phi t x) X)
    (h0 : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (htrans : ∀ q, ¬ ∃ w : TangentSpace (𝓡 n) q,
      mfderiv (𝓡 n) (𝓡 (n + 1)) j q w = X (j q)) :
    letI := RiemannianMetric.lineProductChartedSpace (n := n) (M := S)
    letI := RiemannianMetric.lineProductIsManifold (n := n) (M := S)
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (fun z : S × ℝ => Phi z.2 (j z.1)) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (S × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) S ℝ ℝ
  let := RiemannianMetric.lineProductChartedSpace (n := n) (M := S)
  let := RiemannianMetric.lineProductIsManifold (n := n) (M := S)
  let Gamma : S × ℝ → Q := fun z => Phi z.2 (j z.1)
  have hPhi (t : ℝ) : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (Phi t) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hGamma : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞ Gamma :=
    hs.comp (contMDiff_snd.prodMk (hj.comp contMDiff_fst))
  have hzero (q : S) (w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) (q, (0 : ℝ))) :
      mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma (q, 0) w =
        mfderiv (𝓡 n) (𝓡 (n + 1)) j q w.1 + w.2 • X (j q) := by
    rw [mfderiv_prod_eq_add_apply (hGamma.mdifferentiable (by simp) (q, 0))]
    have hinit : (fun y : S => Gamma (y, 0)) = j := funext (fun y => h0 (j y))
    rw [hinit]
    have ht := (hcurve (j q) 0).mfderiv
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun t => Phi t (j q)) 0 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (Phi 0 (j q))) at ht
    rw [h0] at ht
    change _ + mfderiv 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun t => Phi t (j q)) 0 w.2 = _
    rw [ht]
    rfl
  have hraw0 (q : S) : Function.Injective
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma (q, (0 : ℝ))) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro w hw
    rw [hzero] at hw
    have ha : w.2 = 0 := by
      by_contra ha
      apply htrans q
      refine ⟨-(w.2)⁻¹ • w.1, ?_⟩
      have hjw : mfderiv (𝓡 n) (𝓡 (n + 1)) j q w.1 = -(w.2 • X (j q)) := by
        simpa only [add_sub_cancel_right, zero_sub] using
          congrArg (fun y => y - w.2 • X (j q)) hw
      rw [map_smul, hjw, smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ ha, one_smul]
    have hv : w.1 = 0 := by
      apply hj_inj q
      simpa only [ha, zero_smul, add_zero, map_zero] using hw
    exact Prod.ext hv ha
  let A (t : ℝ) : Q ≃ₘ⟮𝓡 (n + 1), 𝓡 (n + 1)⟯ Q := {
    toEquiv := {
      toFun := Phi t
      invFun := Phi (-t)
      left_inv := fun x => by
        simpa only [neg_add_cancel, h0] using (hadd (-t) t x).symm
      right_inv := fun x => by
        simpa only [add_neg_cancel, h0] using (hadd t (-t) x).symm }
    contMDiff_toFun := hPhi t
    contMDiff_invFun := hPhi (-t) }
  let T (t : ℝ) : (S × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), (𝓡 n).prod 𝓘(ℝ, ℝ)⟯
      (S × ℝ) := {
    toEquiv := {
      toFun := fun z => (z.1, z.2 - t)
      invFun := fun z => (z.1, z.2 + t)
      left_inv := fun z => by simp
      right_inv := fun z => by simp }
    contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
    contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const) }
  have hfactor (t : ℝ) : Gamma = A t ∘ (Gamma ∘ T t) := by
    funext z
    change Phi z.2 (j z.1) = Phi t (Phi (z.2 - t) (j z.1))
    rw [← hadd, add_comm t (z.2 - t), sub_add_cancel]
  have hraw (z : S × ℝ) : Function.Injective
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma z) := by
    have hTz : T z.2 z = (z.1, (0 : ℝ)) := by
      change (z.1, z.2 - z.2) = (z.1, 0)
      rw [sub_self]
    have hmid : Function.Injective
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma (T z.2 z)) := by
      rw [hTz]
      exact hraw0 z.1
    have hderiv : mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma z =
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (A z.2) (Gamma (T z.2 z))).comp
          ((mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma (T z.2 z)).comp
            (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) (T z.2) z)) := by
      conv_lhs => rw [hfactor z.2]
      rw [mfderiv_comp z ((A z.2).mdifferentiable (by simp) _)
        ((hGamma.comp (T z.2).contMDiff).mdifferentiable (by simp) z),
        mfderiv_comp z (hGamma.mdifferentiable (by simp) _)
          ((T z.2).mdifferentiable (by simp) z)]
      rfl
    rw [hderiv]
    exact ((A z.2).mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (hmid.comp ((T z.2).mfderivToContinuousLinearEquiv (by simp) z).injective)
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
  have hflat : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ Gamma :=
    hGamma.comp e.symm.contMDiff
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hflat
  intro z
  have hderiv : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) Gamma z =
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) Gamma (e.symm z)).comp
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm z) :=
    mfderiv_comp z (hGamma.mdifferentiable (by simp) _)
      (e.symm.mdifferentiable (by simp) z)
  have hinj : Function.Injective (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) Gamma z) := by
    rw [hderiv]
    exact (hraw (e.symm z)).comp
      (e.symm.mfderivToContinuousLinearEquiv (by simp) z).injective
  refine ⟨hinj, ?_⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (n + 1)) z) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (n + 1)) (Gamma z)) := by
    unfold TangentSpace
    infer_instance
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) Gamma z).toLinearMap) rfl).mp hinj

end PoincareConjecture.M30
