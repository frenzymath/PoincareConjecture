import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HessianTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


theorem sum_deriv_connection_extend_eq_zero
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let b := (F.metric t).orthonormalBasis x
    ∑ i, (deriv (fun s => (F.connection s).connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)) x) t) (b i) = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let A (i) := (deriv (fun s => (F.connection s).connection
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)) x) t) (b i)
  have hD := D.intrinsicCurvatureTensorCalculus
  have hcoef (i j) : inner ℝ (b j) (A i) =
      -D.frameRicciDerivative x i j i - D.frameRicciDerivative x i j i +
        D.frameRicciDerivative x j i i := by
    rw [real_inner_comm]
    change (F.metric t).inner x (A i) (b j) = _
    rw [F.inner_deriv_connection_extend_of_equation ht]
    change -D.covariantTensorDerivative D.ricciEvaluation x ![b i, b i, b j] -
      D.covariantTensorDerivative D.ricciEvaluation x ![b i, b i, b j] +
      D.covariantTensorDerivative D.ricciEvaluation x ![b j, b i, b i] = _
    rw [D.covariantTensorDerivative_ricciEvaluation_symm hD x (b i) (b i) (b j)]
    rfl
  have hzero (j) : inner ℝ (b j) (∑ i, A i) = 0 := by
    simp only [inner_sum, hcoef, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, D.frameRicciDerivative_trace hD,
      D.frameRicciDerivative_scalar_trace hD]
    ring
  have h := b.sum_repr' (∑ i, A i)
  simp only [hzero, zero_smul, Finset.sum_const_zero] at h
  exact h.symm


theorem hasDerivAt_laplacian_of_time_derivative
    (F : RicciFlow n M J) {f : ℝ × M → ℝ} {df : M → ℝ}
    {t : ℝ} (ht : t ∈ interior J)
    (hspace : ∀ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (s, y)))
    (hreg : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (t, y))
    (hdf : ∀ y, HasDerivAt (fun s => f (s, y)) (df y) t) (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => (F.connection s).laplacian (fun y => f (s, y)) x)
      (D.laplacian df x + 2 * ∑ i, ∑ j,
        D.ricci x (b i) (b j) * D.hessian (fun y => f (t, y)) x (b i) (b j)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let T : ℝ → CovariantTensorEvaluation n M 2 := fun s y v =>
    (F.connection s).hessian (fun z => f (s, z)) y (v 0) (v 1)
  let W : ℝ → CovariantTensorEvaluation n M 2 := fun _ y v =>
    (F.connection t).hessian df y (v 0) (v 1) -
      mvfderiv (𝓡 n) (fun z => f (t, z)) y
        ((deriv (fun s => (F.connection s).connection
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v 1)) y) t) (v 0))
  have hW (v : Fin 2 → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => T s x v) (W t x v) t :=
    F.hasDerivAt_hessian_time ht hspace hreg hdf x (v 0) (v 1)
  have h := F.hasDerivAt_tensorTrace (T := T) (W := W) ht x
    (fun s => (F.connection s).hessian_isSmoothCovariantTensor (hspace s)) hW Fin.elim0
  change HasDerivAt (fun s => (F.connection s).laplacian (fun y => f (s, y)) x) _ t at h
  apply h.congr_deriv
  simp only [RiemannianMetric.tensorTrace, W, T, Fin.cons_zero, Fin.cons_one,
    Finset.sum_sub_distrib, ← map_sum, F.sum_deriv_connection_extend_eq_zero ht, map_zero,
    sub_zero, LeviCivitaData.laplacian]



theorem hasDerivAt_laplacian
    (F : RicciFlow n M J) {f : M × ℝ → ℝ} {t : ℝ}
    (ht : t ∈ interior J)
    (hf : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (univ ×ˢ J))
    (x : M) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => (F.connection s).laplacian (fun y => f (y, s)) x)
      (D.laplacian (fun y => deriv (fun s => f (y, s)) t) x +
        2 * ∑ i, ∑ j, D.ricci x (b i) (b j) *
          D.hessian (fun y => f (y, t)) x (b i) (b j)) t := by
  classical
  let f' : ℝ × M → ℝ := fun p => if p.1 ∈ J then f (p.2, p.1) else 0
  have hnear : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hsmooth (y : M) : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (y, t) :=
    hf.contMDiffAt (prod_mem_nhds Filter.univ_mem hnear)
  have hspace (s : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f' (s, y)) := by
    by_cases hs : s ∈ J
    · have hslice : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => f (y, s)) :=
        contMDiffOn_univ.mp (hf.comp
          (contMDiffOn_id.prodMk contMDiffOn_const) (fun y _ => ⟨mem_univ y, hs⟩))
      simpa only [f', if_pos hs] using hslice
    · simpa only [f', if_neg hs] using
        (contMDiff_const : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)))
  have hreg (y : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f' (t, y) := by
    have hswap : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => f (p.2, p.1)) (t, y) :=
      (hsmooth y).comp_of_eq (contMDiffAt_snd.prodMk contMDiffAt_fst) rfl
    apply hswap.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually hnear] with p hp
    exact if_pos hp
  have hdf (y : M) : HasDerivAt (fun s => f' (s, y))
      (deriv (fun s => f (y, s)) t) t := by
    have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => f (y, s)) t :=
      (hsmooth y).comp t (contMDiffAt_const.prodMk contMDiffAt_id)
    apply (hs.contDiffAt.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [hnear] with s hs
    exact if_pos hs
  have h := F.hasDerivAt_laplacian_of_time_derivative ht hspace hreg hdf x
  have hft : (fun y => f' (t, y)) = (fun y => f (y, t)) := by
    funext y
    exact if_pos (interior_subset ht)
  dsimp only at h ⊢
  rw [hft] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hnear] with s hs
  simp only [f', if_pos hs]

end PoincareConjecture.RicciFlow
