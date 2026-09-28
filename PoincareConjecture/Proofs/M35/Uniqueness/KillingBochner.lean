import PoincareConjecture.Proofs.M35.Uniqueness.InitialKilling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanFields

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)

noncomputable def fieldHessian {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (x u v : V n) : V n :=
  D.connection (fun y => D.connection X y v) x u -
    D.connection X x (D.connection (fun _ => v) x u)

private theorem field_contMDiff {n : ℕ} {X : V n → V n}
    (hX : ContDiff ℝ ∞ X) :
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => Bundle.TotalSpace.mk' (V n) y (E := TangentSpace (𝓡 n)) (X y)) := by
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using hX.contMDiff.contMDiffAt⟩

set_option backward.isDefEq.respectTransparency false in

theorem fieldHessian_pair_skew_of_killing {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (hkill : ∀ y a b, DeTurckNative.metricLieDerivative D X y a b = 0)
    (x u v w : V n) :
    g.inner x (fieldHessian D X x u v) w +
      g.inner x v (fieldHessian D X x u w) = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hC (a : V n) := field_contMDiff (contDiff_const (c := a) :
    ContDiff ℝ ∞ (fun _ : V n => a))
  have hS := field_contMDiff hX
  have hN (a : V n) :
      ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun y => Bundle.TotalSpace.mk' (V n) y
          (E := TangentSpace (𝓡 n)) (D.connection X y a)) := by
    rw [← contMDiffOn_univ]
    exact D.contMDiffOn_connection_apply isOpen_univ (fun _ => a) X
      (hC a).contMDiffOn hS.contMDiffOn
  have hpair₁ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.connection X y v) w) :=
    (hN v).inner_bundle (hC w)
  have hpair₂ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y v (D.connection X y w)) :=
    (hC v).inner_bundle (hN w)
  have hzero : (fun y => g.inner y (D.connection X y v) w +
      g.inner y v (D.connection X y w)) = fun _ => (0 : ℝ) := by
    funext y
    exact (DeTurckNative.metricLieDerivative_apply D X y v w).symm.trans (hkill y v w)
  have hd := congrArg (fun f => mvfderiv (𝓡 n) f x u) hzero
  rw [mvfderiv_fun_add (hpair₁ x |>.mdifferentiableAt (by simp))
      (hpair₂ x |>.mdifferentiableAt (by simp)), mvfderiv_const, zero_apply] at hd
  simp only [add_apply] at hd
  rw [D.mvfderiv_inner (fun _ => u) (fun y => D.connection X y v) (fun _ => w)
      ((hN v x).mdifferentiableAt (by simp)) ((hC w x).mdifferentiableAt (by simp)),
    D.mvfderiv_inner (fun _ => u) (fun _ => v) (fun y => D.connection X y w)
      ((hC v x).mdifferentiableAt (by simp)) ((hN w x).mdifferentiableAt (by simp))] at hd
  have h₁ := hkill x (D.connection (fun _ => v) x u) w
  have h₂ := hkill x v (D.connection (fun _ => w) x u)
  rw [DeTurckNative.metricLieDerivative_apply] at h₁ h₂
  simp only [fieldHessian, map_sub, sub_apply]
  linarith only [hd, h₁, h₂]

set_option backward.isDefEq.respectTransparency false in

theorem fieldHessian_commutator {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x u v : V n) :
    fieldHessian D X x u v - fieldHessian D X x v u =
      D.curvature x u v (X x) := by
  have hC (a : V n) := field_contMDiff (contDiff_const (c := a) :
    ContDiff ℝ ∞ (fun _ : V n => a))
  have hb : VectorField.mlieBracket (𝓡 n) (fun _ : V n => u) (fun _ => v) x = 0 := by
    simp only [VectorField.mlieBracket,
      VectorField.mlieBracketWithin_eq_lieBracketWithin, VectorField.lieBracketWithin,
      fderivWithin_univ, fderiv_const_apply, zero_apply, sub_self]
  have ht := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
    ((hC u x).mdifferentiableAt (by simp)) ((hC v x).mdifferentiableAt (by simp))
  rw [hb] at ht
  have heq := sub_eq_zero.mp ht
  have hR := D.curvatureOnFields_eq_curvature_euclidean
    (X := fun _ => u) (Y := fun _ => v) (Z := X) (x := x)
    contDiffAt_const contDiffAt_const hX.contDiffAt
  simp only [LeviCivitaData.curvatureOnFields, hb, map_zero, sub_zero] at hR
  simp only [fieldHessian, heq]
  rw [← hR]
  abel

theorem killing_hessian_trace_pair {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (hkill : ∀ y a b, DeTurckNative.metricLieDerivative D X y a b = 0)
    (x w : V n) :
    g.inner x (∑ i, fieldHessian D X x
        (g.orthonormalBasis x i) (g.orthonormalBasis x i)) w +
      D.ricci x w (X x) = 0 := by
  classical
  have hterm (e : V n) :
      g.inner x (fieldHessian D X x e e) w +
        g.inner x (D.curvature x e w (X x)) e = 0 := by
    have h₁ := fieldHessian_pair_skew_of_killing D X hX hkill x e e w
    have h₂ := fieldHessian_pair_skew_of_killing D X hX hkill x w e e
    rw [g.symm x e (fieldHessian D X x e w)] at h₁
    rw [g.symm x e (fieldHessian D X x w e)] at h₂
    have hc := congrArg (fun z => g.inner x z e)
      (fieldHessian_commutator D X hX x e w)
    simp only [map_sub, sub_apply] at hc
    linarith only [h₁, h₂, hc]
  have hcurv (e : V n) :
      g.inner x (D.curvature x w e e) (X x) =
        g.inner x (D.curvature x e w (X x)) e := by
    rw [Proofs.M03.curvature_pair_skew D x w e e (X x)]
    have hs : D.curvature x w e (X x) = -D.curvature x e w (X x) :=
      Proofs.M03.curvatureOnFields_swap D _ _ _ x
    rw [hs, map_neg, neg_neg, g.symm]
  simp only [map_sum, sum_apply, LeviCivitaData.ricci, LeviCivitaData.curvatureTensor,
    hcurv, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun i _ => hterm (g.orthonormalBasis x i))

end PoincareConjecture.M35.Uniqueness
