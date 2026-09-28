import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.GaugePullbackMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35.Uniqueness

open DeTurckNative DiffeomorphNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem euclideanConnection_pullback
    (k : RiemannianMetric n V) (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (K : LeviCivitaData k) (D : LeviCivitaData (gaugePullbackMetric k Φ))
    (x u v : V) :
    fderiv ℝ (Φ : V → V) x (D.euclideanConnection u v x) =
      fderiv ℝ (fderiv ℝ (Φ : V → V)) x u v +
        K.euclideanConnection (fderiv ℝ (Φ : V → V) x u)
          (fderiv ℝ (Φ : V → V) x v) (Φ x) := by
  have hΦ : ContDiff ℝ ∞ (Φ : V → V) := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hΨ : ContDiff ℝ ∞ (Φ.symm : V → V) := contMDiff_iff_contDiff.mp Φ.symm.contMDiff
  let Y : V → V := fun y => fderiv ℝ (Φ : V → V) (Φ.symm y) v
  have hY : ContDiff ℝ ∞ Y :=
    ((hΦ.fderiv_right (m := ∞) (by simp)).comp hΨ).clm_apply contDiff_const
  have hYsection (y : V) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V))
      (fun z : V => (⟨z, Y z⟩ : TangentBundle (𝓡 n) V)) y := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by
      simpa using mdifferentiableAt_iff_differentiableAt.mpr
        (hY.differentiable (by simp) y)⟩
  have hYΦ (y : V) : Y (Φ y) = fderiv ℝ (Φ : V → V) y v := by
    simp only [Y, Φ.symm_apply_apply]
  have hpull : pullField Φ Y = fun _ : V => v := by
    funext y
    apply (Φ.mfderivToContinuousLinearEquiv (by simp) y).injective
    change mfderiv (𝓡 n) (𝓡 n) Φ y (pullField Φ Y y) =
      mfderiv (𝓡 n) (𝓡 n) Φ y v
    rw [mfderiv_pullField, hYΦ, mfderiv_eq_fderiv]
    rfl
  have hcomp : Y ∘ (Φ : V → V) = fun y => fderiv ℝ (Φ : V → V) y v :=
    funext hYΦ
  have hd := congrArg (fun L : V →L[ℝ] V => L u)
    (fderiv_comp x (hY.differentiable (by simp) (Φ x))
      (hΦ.differentiable (by simp) x))
  rw [hcomp, fderiv_clm_apply
    ((hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const v)] at hd
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply,
    zero_apply, map_zero, zero_add] at hd
  have ht := connection_pullField_apply k Φ
    (contMDiff_gaugePullback_section k Φ) K D Y (hYsection (Φ x)) u
  rw [hpull, mfderiv_eq_fderiv, K.connection_eq_fderiv_add
    (hY.differentiable (by simp) (Φ x)), hYΦ] at ht
  calc
    _ = fderiv ℝ Y (Φ x) (fderiv ℝ (Φ : V → V) x u) +
        K.euclideanConnection (fderiv ℝ (Φ : V → V) x u)
          (fderiv ℝ (Φ : V → V) x v) (Φ x) := by convert! ht using 1
    _ = _ := by rw [← hd]

theorem mapCovariantHessian_pullback
    (k b : RiemannianMetric n V) (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (K : LeviCivitaData k) (B : LeviCivitaData b)
    (D : LeviCivitaData (gaugePullbackMetric k Φ)) (x u v : V) :
    mapCovariantHessian D B Φ x u v =
      -CovariantDerivative.difference K.connection B.connection (Φ x)
        (fderiv ℝ (Φ : V → V) x v) (fderiv ℝ (Φ : V → V) x u) := by
  rw [mapCovariantHessian_apply, euclideanConnection_pullback k Φ K D,
    connectionDifference_euclidean]
  abel

theorem mapTension_pullback
    (k b : RiemannianMetric n V) (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (K : LeviCivitaData k) (B : LeviCivitaData b)
    (D : LeviCivitaData (gaugePullbackMetric k Φ)) (x : V) :
    mapTension D B Φ x = -intrinsicDeTurckField K B (Φ x) := by
  let e : Module.Basis (Fin n) ℝ V := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
  let e' := e.map A.toLinearEquiv
  let F : Fin n → V → V := fun i _ => e' i
  have he' (i : Fin n) : e' i = fderiv ℝ (Φ : V → V) x (e i) := by
    change A (e i) = _
    have hA := congrArg (fun L => L (e i))
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ (by simp) (x := x))
    simp only [mfderiv_eq_fderiv] at hA
    convert! hA using 1
  have hgram : (frameMetricJet k F (Φ x)).value =
      Matrix.of (fun i j => (gaugePullbackMetric k Φ).inner x (e i) (e j)) := by
    ext i j
    change k.inner (Φ x) (e' i) (e' j) =
      (gaugePullbackMetric k Φ).inner x (e i) (e j)
    rw [gaugePullbackMetric_inner, he', he']
  rw [mapTension_eq_inverse_gram D B Φ x e,
    intrinsicDeTurckField_eq_frame_contraction K B F (Φ x) e' (fun _ => rfl),
    hgram, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [mapCovariantHessian_pullback k b Φ K B D, smul_neg]
  simp only [F, he']

end PoincareConjecture.M35.Uniqueness
