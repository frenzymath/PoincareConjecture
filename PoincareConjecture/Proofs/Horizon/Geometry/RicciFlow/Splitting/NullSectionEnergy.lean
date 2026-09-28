import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.CurvatureNullity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Contact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantRicciDerivative_on_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, ∀ w, D.ricci y (V y) w = 0)
    (a w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.ricciEvaluation x ![a, V x, w] =
      -D.ricci x (D.connection V x a) w := by
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  have hW := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) w
  have heq : (fun y => D.ricci y (V y) (W y)) =ᶠ[𝓝 x] fun _ => 0 :=
    hnull.mono fun y hy => hy (W y)
  have h := D.covariantTensorDerivative_two_on_fields hD.2.1 V W x
    (hV.mdifferentiableAt (by simp)) (hW.mdifferentiableAt (by simp)) a
  simp only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
    W, FiberBundle.extend_apply_self] at h
  rw [Poincare.mvfderiv_eq_of_eventuallyEq heq, mvfderiv_const] at h
  simpa only [zero_apply, hnull.self_of_nhds _, sub_zero, zero_sub] using h

theorem secondCovariantRicciDerivative_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, ∀ w, D.ricci y (V y) w = 0)
    (a : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation)
        x ![a, a, V x, V x] =
      2 * D.ricci x (D.connection V x a) (D.connection V x a) := by
  have hsym (y : M) (u v : TangentSpace (𝓡 n) y) :
      D.ricci y u v = D.ricci y v u := (hD.2.2.2.1 y u v u v).2.2.2
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let W : Fin 2 → (y : M) → TangentSpace (𝓡 n) y := fun _ => V
  have hessian_zero : D.hessian (fun y => D.ricci y (V y) (V y)) x a a = 0 := by
    rw [D.hessian_eq_of_eventuallyEq (hnull.mono fun y hy => hy (V y))]
    simp [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields, mvfderiv_const]
  have h := D.secondCovariantTensorDerivative_on_fields hD.2.1 W x (fun _ => hV) a a
  dsimp only [W] at h
  simp only [Fin.sum_univ_two, LeviCivitaData.ricciEvaluation,
    Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h
  have hsum_deriv : mvfderiv (𝓡 n) (fun y =>
      D.ricci y (D.covariantDerivativeOnFields Y V y) (V y) +
        D.ricci y (V y) (D.covariantDerivativeOnFields Y V y)) x a = 0 := by
    have he : (fun y => D.ricci y (D.covariantDerivativeOnFields Y V y) (V y) +
        D.ricci y (V y) (D.covariantDerivativeOnFields Y V y)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hnull] with y hy
      simp only [hsym y _ (V y), hy, add_zero]
    rw [Poincare.mvfderiv_eq_of_eventuallyEq he, mvfderiv_const]
    rfl
  have htuples (v z : TangentSpace (𝓡 n) x) :
      Fin.cons a (Function.update (fun _ : Fin 2 => v) 0 z) = ![a, z, v] ∧
        Fin.cons a (Function.update (fun _ : Fin 2 => v) 1 z) = ![a, v, z] := by
    constructor <;> ext i <;> fin_cases i <;> rfl
  rw [(htuples _ _).1, (htuples _ _).2] at h
  have hleft := covariantRicciDerivative_on_null_section D hD V hV hnull a
    (D.connection V x a)
  have hright := D.covariantTensorDerivative_ricciEvaluation_symm hD x a
    (D.connection V x a) (V x)
  have hmiddle : D.ricci x (D.connection V x (D.connection Y x a)) (V x) +
      D.ricci x (V x) (D.connection V x (D.connection Y x a)) = 0 := by
    simp only [hsym x _ (V x), hnull.self_of_nhds, add_zero]
  have heval : Fin.cons a (Fin.cons a (fun _ : Fin 2 => V x)) = ![a, a, V x, V x] := by
    ext i
    fin_cases i <;> rfl
  rw [heval] at h
  rw [hessian_zero, hsum_deriv, hmiddle, hright, hleft] at h
  linarith

theorem tensorLaplacian_ricci_null_section
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, ∀ w, D.ricci y (V y) w = 0) :
    D.tensorLaplacian D.ricciEvaluation x ![V x, V x] =
      2 * ∑ i, D.ricci x (D.connection V x (g.orthonormalBasis x i))
        (D.connection V x (g.orthonormalBasis x i)) := by
  rw [Finset.mul_sum]
  unfold LeviCivitaData.tensorLaplacian
  apply Finset.sum_congr rfl
  intro i _
  exact secondCovariantRicciDerivative_null_section D hD V hV hnull _

theorem ricci_connection_eq_zero_of_terminal_null
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (V : (y : M) → TangentSpace (𝓡 n) y) {x : M}
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) x)
    (hnull : ∀ᶠ y in 𝓝 x, (F.connection b).ricci y (V y) (V y) = 0)
    (u w : TangentSpace (𝓡 n) x) :
    (F.connection b).ricci x ((F.connection b).connection V x u) w = 0 := by
  let D := F.connection b
  let g := F.metric b
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hD : D.CurvatureTensorCalculus := hC.tensor_calculus n M g D
  have hRic (t : ℝ) (ht : t ∈ Icc a b) (y : M) (v : TangentSpace (𝓡 n) y) :
      0 ≤ (F.connection t).ricci y v v :=
    Finset.sum_nonneg fun i _ => hsec t ht y v ((F.metric t).orthonormalBasis y i)
  have hn : ∀ᶠ y in 𝓝 x, ∀ z, D.ricci y (V y) z = 0 := by
    filter_upwards [hnull] with y hy
    exact ricci_eq_zero_of_nonneg_of_self_eq_zero D hD y (hRic b hb y) hy
  have hd := hC.ricci_evolution n M (Icc a b) F b hb x (V x) (V x)
  have hmin : IsLocalMinOn (fun t => (F.connection t).ricci x (V x) (V x))
      (Icc a b) b := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [hnull.self_of_nhds] using hRic t ht x (V x)
  have hcone : a - b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset hb ⟨le_rfl, hab.le⟩)
  have hsign := hmin.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hsign
  have hreact : D.ricciReaction x (V x) (V x) = 0 :=
    ricciReaction_eq_zero_of_ricci_self_eq_zero D hD x (hsec b hb x)
      hnull.self_of_nhds (V x)
  have henergy := tensorLaplacian_ricci_null_section D hD V hV hn
  change 0 ≤ (a - b) * (D.tensorLaplacian D.ricciEvaluation x ![V x, V x] +
    D.ricciReaction x (V x) (V x)) at hsign
  rw [hreact, add_zero, henergy] at hsign
  have hsum : (∑ i, D.ricci x (D.connection V x (g.orthonormalBasis x i))
      (D.connection V x (g.orthonormalBasis x i))) = 0 := by
    have hnonneg := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      hRic b hb x (D.connection V x (g.orthonormalBasis x i))
    nlinarith
  have hdiag (i) : D.ricci x (D.connection V x (g.orthonormalBasis x i))
      (D.connection V x (g.orthonormalBasis x i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hRic b hb x
      (D.connection V x (g.orthonormalBasis x j)))).mp hsum i (Finset.mem_univ i)
  have hbasis (i) : D.ricci x (D.connection V x (g.orthonormalBasis x i)) w = 0 :=
    ricci_eq_zero_of_nonneg_of_self_eq_zero D hD x (hRic b hb x) (hdiag i) w
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have hB (v z : TangentSpace (𝓡 n) x) : B v z = D.ricci x v z := by
    simp [B, LeviCivitaData.ricci, LinearMap.sum_apply, g]
  let L := (B.flip w).comp (D.connection V x).toLinearMap
  have hL (v : TangentSpace (𝓡 n) x) : L v = D.ricci x (D.connection V x v) w := by
    change B ((D.connection V x) v) w = _
    exact hB _ _
  have hLb (i) : L (g.orthonormalBasis x i) = 0 := (hL _).trans (hbasis i)
  have hLu : L u = 0 := by
    rw [← (g.orthonormalBasis x).sum_repr' u]
    simp only [map_sum, map_smul, hLb, smul_zero, Finset.sum_const_zero]
  exact (hL u).symm.trans hLu

end PoincareConjecture.RicciFlow.Splitting
