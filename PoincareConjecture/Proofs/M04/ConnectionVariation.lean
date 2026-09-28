import PoincareConjecture.Proofs.M04.ConnectionDifference
import PoincareConjecture.Proofs.M04.MixedTimeSpatial
import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 2500000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_connection_pairing (F : RicciFlow n M J)
    {U : Set M} {X Y Z : (y : M) → TangentSpace (𝓡 n) y} {t : ℝ} {x : M}
    (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (ht : t ∈ interior J) (hx : x ∈ U) :
    HasDerivAt (fun s ↦ (F.metric t).inner x ((F.connection s).connection Y x (X x)) (Z x))
      (-(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
          x ![X x, Y x, Z x] -
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
          x ![Y x, X x, Z x] +
        (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
          x ![Z x, X x, Y x]) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) x
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let D := F.connection t
  let A : ℝ → E := fun s ↦ (F.connection s).connection Y x (X x) - D.connection Y x (X x)
  let H : ℝ → CovariantTensorEvaluation n M 2 :=
    fun s y v ↦ (F.metric s).inner y (v 0) (v 1) - (F.metric t).inner y (v 0) (v 1)
  let K (P Q R : (y : M) → TangentSpace (𝓡 n) y) :=
    covariantTensorDerivativeOnFields D D.ricciEvaluation ![P, Q, R] x
  have hAt : A t = 0 := sub_self _
  have hg (y : M) (a b : TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s ↦ (F.metric s).inner y a b) (-2 * D.ricci y a b) t :=
    (F.equation t (interior_subset ht) y a b).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
  have hmetric {V : Set M} {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) V)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) V) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ (F.metric p.1).inner p.2 (P p.2) (Q p.2)) (J ×ˢ V) := by
    have hP' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (P p.2))
        (J ×ˢ V) := hP.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
    have hQ' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Q p.2))
        (J ×ˢ V) := hQ.comp contMDiffOn_snd (fun _ hp ↦ hp.2)
    intro p hp
    have hm := (F.smooth p ⟨hp.1, mem_univ p.2⟩).mono
      (show J ×ˢ V ⊆ J ×ˢ univ from fun q hq ↦ ⟨hq.1, mem_univ q.2⟩)
    have he : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun q ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
          ((F.metric q.1).inner q.2 (P q.2) (Q q.2))) (J ×ˢ V) p :=
      hm.clm_bundle_apply₂ (hP' p hp) (hQ' p hp)
    simp only [Bundle.contMDiffWithinAt_totalSpace] at he
    exact he.2
  have hC {V : Set M} (hV : IsOpen V)
      {P Q R : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) V)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) V)
      (hR : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% R) V)
      (hxV : x ∈ V) :
      HasDerivAt (fun s ↦ covariantTensorDerivativeOnFields D (H s) ![P, Q, R] x)
        (-2 * K P Q R) t := by
    have hQd := (hQ.contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    have hRd := (hR.contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    have hGerm (g : RiemannianMetric n M) : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y ↦ g.inner y (Q y) (R y)) x := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact hQd.inner_bundle hRd
    have hRic := ((contMDiffOn_ricci D hV hQ hR).contMDiffAt
      (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    have hspace := hasDerivAt_mvfderiv_time hV (hmetric hQ hR) ht hxV
      (fun y _ ↦ hg y (Q y) (R y)) (P x)
    have hv : mvfderiv (𝓡 n) (fun y ↦ -2 * D.ricci y (Q y) (R y)) x (P x) =
        -2 * mvfderiv (𝓡 n) (fun y ↦ D.ricci y (Q y) (R y)) x (P x) := by
      erw [mvfderiv_fun_mul mdifferentiableAt_const hRic]
      simp only [mvfderiv_const, add_apply, smul_apply, zero_apply, mul_zero, add_zero, smul_eq_mul]
    have hd0 := (hspace.congr_deriv hv).sub_const
      (mvfderiv (𝓡 n) (fun y ↦ (F.metric t).inner y (Q y) (R y)) x (P x))
    have hd1 := (hg x (D.connection Q x (P x)) (R x)).sub_const
      ((F.metric t).inner x (D.connection Q x (P x)) (R x))
    have hd2 := (hg x (Q x) (D.connection R x (P x))).sub_const
      ((F.metric t).inner x (Q x) (D.connection R x (P x)))
    have heq (s : ℝ) : covariantTensorDerivativeOnFields D (H s) ![P, Q, R] x =
        (mvfderiv (𝓡 n) (fun y ↦ (F.metric s).inner y (Q y) (R y)) x (P x) -
          mvfderiv (𝓡 n) (fun y ↦ (F.metric t).inner y (Q y) (R y)) x (P x)) -
        (((F.metric s).inner x (D.connection Q x (P x)) (R x) -
            (F.metric t).inner x (D.connection Q x (P x)) (R x)) +
          ((F.metric s).inner x (Q x) (D.connection R x (P x)) -
            (F.metric t).inner x (Q x) (D.connection R x (P x)))) := by
      simp only [covariantTensorDerivativeOnFields, Fin.sum_univ_succ]
      change mvfderiv (𝓡 n) (fun y ↦ (F.metric s).inner y (Q y) (R y) -
          (F.metric t).inner y (Q y) (R y)) x (P x) -
        (((F.metric s).inner x (D.connection Q x (P x)) (R x) -
            (F.metric t).inner x (D.connection Q x (P x)) (R x)) +
          (((F.metric s).inner x (Q x) (D.connection R x (P x)) -
            (F.metric t).inner x (Q x) (D.connection R x (P x))) + 0)) = _
      erw [mvfderiv_sub (hGerm (F.metric s)) (hGerm (F.metric t))]
      simp only [sub_apply, add_zero]
    apply ((hd0.sub (hd1.add hd2)).congr_of_eventuallyEq
      (Eventually.of_forall heq)).congr_deriv
    simp only [K, covariantTensorDerivativeOnFields, Fin.sum_univ_succ]
    change -2 * mvfderiv (𝓡 n) (fun y ↦ D.ricci y (Q y) (R y)) x (P x) -
        (-2 * D.ricci x (D.connection Q x (P x)) (R x) +
          -2 * D.ricci x (Q x) (D.connection R x (P x))) =
      -2 * (mvfderiv (𝓡 n) (fun y ↦ D.ricci y (Q y) (R y)) x (P x) -
        (D.ricci x (D.connection Q x (P x)) (R x) +
          (D.ricci x (Q x) (D.connection R x (P x)) + 0)))
    ring
  have hPair {V : Set M} (hV : IsOpen V)
      (hXV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) V)
      (hYV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) V)
      {W : (y : M) → TangentSpace (𝓡 n) y}
      (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) V)
      (hxV : x ∈ V) :
      HasDerivAt (fun s ↦ (F.metric s).inner x (A s) (W x))
        (-K X Y W - K Y X W + K W X Y) t := by
    have hXd := (hXV.contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    have hYd := (hYV.contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    have hWd := (hW.contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    have hd := ((hC hV hXV hYV hW hxV).add (hC hV hYV hXV hW hxV)).sub
      (hC hV hW hXV hYV hxV)
    have hd' : HasDerivAt (fun s ↦ 2 * (F.metric s).inner x (A s) (W x))
        ((-2 * K X Y W + -2 * K Y X W) - -2 * K W X Y) t :=
      hd.congr_of_eventuallyEq (Eventually.of_forall fun s ↦
        connection_difference_pairing D (F.connection s) hXd hYd hWd)
    have heq : (fun s ↦ (2 * (F.metric s).inner x (A s) (W x)) / 2) =
        (fun s ↦ (F.metric s).inner x (A s) (W x)) := by
      funext s
      ring
    have hd'' := hd'.div_const 2
    rw [heq] at hd''
    apply hd''.congr_deriv
    ring
  have hclm {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
      {L : ℝ → V →L[ℝ] W}
      (hL : ∀ v, DifferentiableAt ℝ (fun s ↦ L s v) t) :
      DifferentiableAt ℝ L t := by
    let d := Module.finrank ℝ V
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e1 := ContinuousLinearEquiv.ofFinrankEq hd
    let e2 := (e1.arrowCongr (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing (Fin d))
    have hc : DifferentiableAt ℝ (fun s ↦ e2 (L s)) t :=
      differentiableAt_pi.mpr fun _ ↦ hL _
    have he := e2.symm.toContinuousLinearMap.differentiableAt.comp t hc
    have heq : (fun s ↦ e2.symm (e2 (L s))) = L := by
      funext s
      exact e2.symm_apply_apply (L s)
    have he' : DifferentiableAt ℝ (fun s ↦ e2.symm (e2 (L s))) t := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! he
    rwa [heq] at he'
  let G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ (F.metric s).inner x
  let Pdual : ℝ → E →L[ℝ] ℝ := fun s ↦ G s (A s)
  have hGd : DifferentiableAt ℝ G t := by
    apply hclm (V := E) (W := E →L[ℝ] ℝ) (L := G)
    intro a
    apply hclm (V := E) (W := ℝ) (L := fun s ↦ G s a)
    intro b
    exact (hg x a b).differentiableAt
  have hPd : DifferentiableAt ℝ Pdual t := by
    apply hclm (V := E) (W := ℝ) (L := Pdual)
    intro w
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
    let V := U ∩ e.baseSet
    have hV : IsOpen V := hU.inter e.open_baseSet
    have hxV : x ∈ V := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
    let W : (y : M) → TangentSpace (𝓡 n) y :=
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (show TangentSpace (𝓡 n) x from w)
    have hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% W) V := (contMDiffOn_extend_baseSet (n := n) (M := M) (x := x) w).mono
          inter_subset_right
    have he := hPair hV (hX.mono inter_subset_left) (hY.mono inter_subset_left) hW hxV
    simpa only [W, FiberBundle.extend_apply_self] using! he.differentiableAt
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let B : ℝ → E →L[ℝ] E := fun s ↦ Q.toContinuousLinearMap.comp (G s)
  have hBd : DifferentiableAt ℝ B t :=
    (differentiableAt_const Q.toContinuousLinearMap).clm_comp hGd
  have hInv (s : ℝ) : (B s).IsInvertible := by
    have hz (a : E) (ha : B s a = 0) : a = 0 := by
      have hg0 : G s a = 0 := Q.injective (by simpa [B] using ha)
      have hi : (F.metric s).inner x a a = 0 := by
        simpa [G] using congrArg (fun L : E →L[ℝ] ℝ ↦ L a) hg0
      by_contra hne
      exact (ne_of_gt ((F.metric s).pos x a hne)) hi
    have hinj : Function.Injective (B s) := by
      intro a b h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (B s) := LinearMap.injective_iff_surjective.mp hinj
    exact ⟨(LinearEquiv.ofBijective (B s).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext a; rfl⟩
  have hBi : DifferentiableAt ℝ (fun s ↦ (B s).inverse) t :=
    (((hInv t).contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)).comp t hBd
  have hrec : DifferentiableAt ℝ (fun s ↦ (B s).inverse (Q (Pdual s))) t :=
    hBi.clm_apply (Q.toContinuousLinearMap.differentiableAt.comp t hPd)
  have hAd : DifferentiableAt ℝ A t := by
    apply hrec.congr_of_eventuallyEq
    exact Eventually.of_forall fun s ↦ ((hInv s).inverse_apply_self (A s)).symm
  have hMove : HasDerivAt (fun s ↦ (F.metric s).inner x (A s) (Z x))
      (G t (deriv A t) (Z x)) t := by
    have hGtime : HasDerivAt G (deriv G t) t := hGd.hasDerivAt
    simpa only [hAt, map_zero, zero_apply, zero_add, add_zero] using!
      (hGtime.clm_apply (F := E) (G := E →L[ℝ] ℝ) hAd.hasDerivAt).clm_apply
        (F := E) (G := ℝ) (hasDerivAt_const t (Z x : E))
  have hVelocity : G t (deriv A t) (Z x) = -K X Y Z - K Y X Z + K Z X Y :=
    hMove.unique (hPair hU hX hY hZ hx)
  have hdConn : HasDerivAt (fun s ↦ (F.connection s).connection Y x (X x))
      (deriv A t) t := by
    have heq : (fun s ↦ A s + D.connection Y x (X x)) =
        (fun s ↦ (F.connection s).connection Y x (X x)) := by
      funext s
      dsimp only [A]
      abel
    simpa only [heq] using hAd.hasDerivAt.add_const (D.connection Y x (X x))
  have hFixed : HasDerivAt
      (fun s ↦ (F.metric t).inner x ((F.connection s).connection Y x (X x)) (Z x))
      (G t (deriv A t) (Z x)) t := by
    have hGconst : HasDerivAt (fun _ : ℝ ↦ G t) (0 : E →L[ℝ] E →L[ℝ] ℝ) t :=
      hasDerivAt_const t (G t)
    simpa only [map_zero, zero_apply, zero_add, add_zero] using!
      (hGconst.clm_apply (F := E) (G := E →L[ℝ] ℝ) hdConn).clm_apply
        (F := E) (G := ℝ) (hasDerivAt_const t (Z x : E))
  have hPointwise {P Q R : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      (hR : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% R) U) :
      K P Q R = D.covariantTensorDerivative D.ricciEvaluation x ![P x, Q x, R x] := by
    have hTup (i : Fin 3) : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (![P, Q, R] i)) U := by
      fin_cases i
      · exact hP
      · exact hQ
      · exact hR
    have he := covariantTensorDerivativeOnFields_eq D
      (isSmoothCovariantTensor_ricciEvaluation D) hU hTup hx
    calc
      K P Q R = D.covariantTensorDerivative D.ricciEvaluation x
          (fun i ↦ ![P, Q, R] i x) := he
      _ = _ := by
        congr 1
        ext i
        fin_cases i <;> rfl
  apply hFixed.congr_deriv
  rw [hVelocity, hPointwise hX hY hZ, hPointwise hY hX hZ, hPointwise hZ hX hY]

end PoincareConjecture.M04
