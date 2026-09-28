import PoincareConjecture.Proofs.M35.Uniqueness.KillingCovector
import PoincareConjecture.Proofs.M35.Uniqueness.KillingDerivativeBianchi

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)

noncomputable def killingRicciCovector {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) : CovariantTensorEvaluation n (V n) 1 :=
  fun x v => D.ricci x (v 0) (X x)

theorem isSmoothCovariantTensor_killingRicciCovector {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) :
    IsSmoothCovariantTensor (killingRicciCovector D X) := by
  refine ⟨fun x => ⟨MultilinearMap.ofSubsingleton ℝ (TangentSpace (𝓡 n) x) ℝ
    (0 : Fin 1) (((DeTurckNative.intrinsicRicciBilin D x).flip (X x)).toLinearMap),
      fun _ => by simp [killingRicciCovector]⟩, ?_⟩
  intro U hU Y hY
  exact M04.contMDiffOn_ricci D hU (hY 0)
    (euclidean_field_contMDiff hX).contMDiffOn

theorem killingRicciCovector_derivative {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x a b : V n) :
    D.covariantTensorDerivative (killingRicciCovector D X) x ![a, b] =
      D.covariantTensorDerivative D.ricciEvaluation x ![a, b, X x] +
        D.ricci x b (D.connection X x a) := by
  have hC (v : V n) := euclidean_field_contMDiff (contDiff_const (c := v) :
    ContDiff ℝ ∞ (fun _ : V n => v))
  have hF : ∀ i : Fin 3, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => Bundle.TotalSpace.mk' (V n) y (E := TangentSpace (𝓡 n))
        (![fun _ => a, fun _ => b, X] i y)) univ := by
    intro i
    fin_cases i
    · exact (hC a).contMDiffOn
    · exact (hC b).contMDiffOn
    · exact (euclidean_field_contMDiff hX).contMDiffOn
  have hR := M04.covariantTensorDerivativeOnFields_eq D
    (M04.isSmoothCovariantTensor_ricciEvaluation D) isOpen_univ
    (X := ![fun _ => a, fun _ => b, X]) hF (x := x) (mem_univ x)
  have hA := M04.covariantTensorDerivativeOnFields_eq D
    (isSmoothCovariantTensor_killingRicciCovector D X hX) isOpen_univ
    (X := fun i _ => (![a, b] : Fin 2 → V n) i)
    (fun i => (hC _).contMDiffOn) (x := x) (mem_univ x)
  have htup : (fun i : Fin 3 => (![fun _ => a, fun _ => b, X] i) x) = ![a, b, X x] := by
    ext i
    fin_cases i <;> rfl
  rw [htup] at hR
  simp only [M04.covariantTensorDerivativeOnFields, LeviCivitaData.ricciEvaluation,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, killingRicciCovector] at hR hA
  change mvfderiv (𝓡 n) (fun y => D.ricci y b (X y)) x a -
    (D.ricci x (D.connection (fun _ => b) x a) (X x) +
      D.ricci x b (D.connection X x a)) =
        D.covariantTensorDerivative D.ricciEvaluation x ![a, b, X x] at hR
  change mvfderiv (𝓡 n) (fun y => D.ricci y b (X y)) x a -
    D.ricci x (D.connection (fun _ => b) x a) (X x) =
      D.covariantTensorDerivative (killingRicciCovector D X) x ![a, b] at hA
  linarith only [hR, hA]

theorem killingRicciCovector_derivative_frame {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x a b : V n) :
    D.covariantTensorDerivative (killingRicciCovector D X) x ![a, b] =
      (∑ q, D.covariantTensorDerivative D.ricciEvaluation x
        ![a, b, g.orthonormalBasis x q] *
          killingCovector g X x ![g.orthonormalBasis x q]) +
      (∑ q, D.ricci x b (g.orthonormalBasis x q) *
        D.covariantTensorDerivative (killingCovector g X) x
          ![a, g.orthonormalBasis x q]) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := g.orthonormalBasis x
  have hrepr (z : TangentSpace (𝓡 n) x) :
      (∑ q, g.inner x z (e q) • e q) = z := by
    have h := e.sum_repr' z
    change (∑ q, g.inner x (e q) z • e q) = z at h
    simpa only [g.symm x] using h
  obtain ⟨R, hR⟩ := (M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (M04.isSmoothCovariantTensor_ricciEvaluation D)).1 x
  have hslot (z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b, X x] (2 : Fin 3) z = ![a, b, z] := by
    ext i
    fin_cases i <;> simp
  have hfirst : D.covariantTensorDerivative D.ricciEvaluation x ![a, b, X x] =
      ∑ q, D.covariantTensorDerivative D.ricciEvaluation x ![a, b, e q] *
        killingCovector g X x ![e q] := by
    rw [hR]
    have h := congrArg (fun z => R (Function.update ![a, b, X x] 2 z)) (hrepr (X x))
    rw [R.map_update_sum] at h
    simp only [R.map_update_smul, smul_eq_mul] at h
    simp only [hslot] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro q _
    rw [← hR]
    exact mul_comm _ _
  have hsecond : D.ricci x b (D.connection X x a) =
      ∑ q, D.ricci x b (e q) *
        D.covariantTensorDerivative (killingCovector g X) x ![a, e q] := by
    have h := congrArg (DeTurckNative.intrinsicRicciBilin D x b)
      (hrepr (D.connection X x a))
    simp only [map_sum, map_smul, smul_eq_mul,
      DeTurckNative.intrinsicRicciBilin_apply] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro q _
    rw [killingCovector_derivative D X hX]
    exact mul_comm _ _
  rw [killingRicciCovector_derivative D X hX, hfirst, hsecond]

end PoincareConjecture.M35.Uniqueness
