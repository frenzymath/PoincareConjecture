import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.GradientTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem differential_square_isSmooth {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothCovariantTensor (k := 2)
      (fun x v ↦ mvfderiv (𝓡 n) f x (v 0) * mvfderiv (𝓡 n) f x (v 1)) := by
  constructor
  · intro x
    refine ⟨{
      toFun := fun v ↦ mvfderiv (𝓡 n) f x (v 0) * mvfderiv (𝓡 n) f x (v 1)
      map_update_add' := ?_
      map_update_smul' := ?_ }, fun _ ↦ rfl⟩
    · intro _ v i a b
      fin_cases i <;> simp [map_add, add_mul, mul_add]
    · intro _ v i c a
      fin_cases i <;> simp [map_smul, mul_assoc, mul_left_comm]
  · intro U hU X hX
    exact ((differentialEvaluation_isSmooth hf).2 U hU
      (fun _ ↦ X 0) (fun _ ↦ hX 0)).mul
      ((differentialEvaluation_isSmooth hf).2 U hU
        (fun _ ↦ X 1) (fun _ ↦ hX 1))

private theorem ricci_gradient_eq_sum {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    D.ricci x (D.gradient f x) (D.gradient f x) =
      ∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
        (mvfderiv (𝓡 n) f x (g.orthonormalBasis x i) *
          mvfderiv (𝓡 n) f x (g.orthonormalBasis x j)) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let B := ∑ k, D.curvatureTensor_bilinear_first_third x (b k) (b k)
  have hB (u v : TangentSpace (𝓡 n) x) : B u v = D.ricci x u v := by
    simp only [B, LinearMap.sum_apply,
      LeviCivitaData.curvatureTensor_bilinear_first_third_apply, LeviCivitaData.ricci, b]
  have hgrad : (∑ i, mvfderiv (𝓡 n) f x (b i) • b i) = D.gradient f x := by
    have hinner (i) : inner ℝ (b i) (D.gradient f x) = mvfderiv (𝓡 n) f x (b i) := by
      change g.inner x (b i) (D.gradient f x) = _
      rw [g.symm, D.inner_gradient]
    have h := b.sum_repr (D.gradient f x)
    simpa only [OrthonormalBasis.repr_apply_apply, hinner] using h
  rw [← hB, ← hgrad]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

namespace RicciFlow

variable {J : Set ℝ}


theorem hasDerivAt_gradient_normSq_of_time_derivative
    (F : RicciFlow n M J) {f : ℝ × M → ℝ} {df : M → ℝ}
    {t : ℝ} (ht : t ∈ interior J)
    (hspace : ∀ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (s, y)))
    (hreg : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, y))
    (hdf : ∀ y, HasDerivAt (fun s ↦ f (s, y)) (df y) t) (x : M) :
    HasDerivAt
      (fun s ↦ (F.metric s).inner x
        ((F.connection s).gradient (fun y ↦ f (s, y)) x)
        ((F.connection s).gradient (fun y ↦ f (s, y)) x))
      (2 * (F.connection t).ricci x
          ((F.connection t).gradient (fun y ↦ f (t, y)) x)
          ((F.connection t).gradient (fun y ↦ f (t, y)) x) +
        2 * (F.metric t).inner x
          ((F.connection t).gradient (fun y ↦ f (t, y)) x)
          ((F.connection t).gradient df x)) t := by
  let T : ℝ → CovariantTensorEvaluation n M 2 := fun s y v ↦
    mvfderiv (𝓡 n) (fun z ↦ f (s, z)) y (v 0) *
      mvfderiv (𝓡 n) (fun z ↦ f (s, z)) y (v 1)
  let W : ℝ → CovariantTensorEvaluation n M 2 := fun _ y v ↦
    mvfderiv (𝓡 n) df y (v 0) * mvfderiv (𝓡 n) (fun z ↦ f (t, z)) y (v 1) +
      mvfderiv (𝓡 n) (fun z ↦ f (t, z)) y (v 0) * mvfderiv (𝓡 n) df y (v 1)
  have hW (v : Fin 2 → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s ↦ T s x v) (W t x v) t :=
    (Poincare.Manifold.hasDerivAt_mvfderiv_time (hreg x) hdf (v 0)).mul
      (Poincare.Manifold.hasDerivAt_mvfderiv_time (hreg x) hdf (v 1))
  have h := F.hasDerivAt_tensorTrace (T := T) (W := W) ht x
    (fun s ↦ differential_square_isSmooth (hspace s)) hW (Fin.elim0)
  have htrace (s : ℝ) : (F.metric s).tensorTrace (T s) x Fin.elim0 =
      (F.metric s).inner x ((F.connection s).gradient (fun y ↦ f (s, y)) x)
        ((F.connection s).gradient (fun y ↦ f (s, y)) x) := by
    simpa only [RiemannianMetric.tensorTrace, T, Fin.cons_zero, Fin.cons_one, pow_two] using
      ((F.connection s).gradient_normSq_eq_sum_mvfderiv_sq (fun y ↦ f (s, y)) x).symm
  simp_rw [htrace] at h
  apply h.congr_deriv
  simp only [RiemannianMetric.tensorTrace, W, T, Fin.cons_zero, Fin.cons_one,
    Finset.sum_add_distrib]
  rw [(F.connection t).sum_mvfderiv_mul_eq_inner_gradient,
    (F.connection t).sum_mvfderiv_mul_eq_inner_gradient,
    ← ricci_gradient_eq_sum]
  rw [(F.metric t).symm x ((F.connection t).gradient df x)]
  ring



theorem hasDerivAt_gradient_normSq
    (F : RicciFlow n M J) {f : M × ℝ → ℝ} {t : ℝ}
    (ht : t ∈ interior J)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (x : M) :
    HasDerivAt
      (fun s ↦ (F.metric s).inner x
        ((F.connection s).gradient (fun y ↦ f (y, s)) x)
        ((F.connection s).gradient (fun y ↦ f (y, s)) x))
      (2 * (F.connection t).ricci x
          ((F.connection t).gradient (fun y ↦ f (y, t)) x)
          ((F.connection t).gradient (fun y ↦ f (y, t)) x) +
        2 * (F.metric t).inner x
          ((F.connection t).gradient (fun y ↦ f (y, t)) x)
          ((F.connection t).gradient (fun y ↦ deriv (fun s ↦ f (y, s)) t) x)) t := by
  classical
  let f' : ℝ × M → ℝ := fun p ↦ if p.1 ∈ J then f (p.2, p.1) else 0
  have hnear : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hsmooth (y : M) : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (y, t) :=
    hf.contMDiffAt (prod_mem_nhds Filter.univ_mem hnear)
  have hspace (s : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f' (s, y)) := by
    by_cases hs : s ∈ J
    · have hslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, s)) :=
        contMDiffOn_univ.mp (hf.comp
          (contMDiffOn_id.prodMk contMDiffOn_const) (fun y _ ↦ ⟨mem_univ y, hs⟩))
      simpa only [f', if_pos hs] using hslice
    · simpa only [f', if_neg hs] using
        (contMDiff_const : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ (0 : ℝ)))
  have hreg (y : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f' (t, y) := by
    have hswap : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ f (p.2, p.1)) (t, y) :=
      (hsmooth y).comp_of_eq (contMDiffAt_snd.prodMk contMDiffAt_fst) rfl
    apply hswap.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually hnear] with p hp
    exact if_pos hp
  have hdf (y : M) : HasDerivAt (fun s ↦ f' (s, y))
      (deriv (fun s ↦ f (y, s)) t) t := by
    have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s ↦ f (y, s)) t :=
      (hsmooth y).comp t (contMDiffAt_const.prodMk contMDiffAt_id)
    apply (hs.contDiffAt.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [hnear] with s hs
    exact if_pos hs
  have h := F.hasDerivAt_gradient_normSq_of_time_derivative ht hspace hreg hdf x
  have hft : (fun y ↦ f' (t, y)) = (fun y ↦ f (y, t)) := by
    funext y
    exact if_pos (interior_subset ht)
  rw [hft] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hnear] with s hs
  simp only [f', if_pos hs]

end RicciFlow

end PoincareConjecture
