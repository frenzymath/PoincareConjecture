import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Riccati
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Symmetric

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.RiemannianMetric

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_operator_inverse
    {J : ℝ → E →L[ℝ] E} {J' : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J J' t)
    (hinv : ∀ᶠ s in 𝓝 t, (J s).IsInvertible) :
    HasDerivAt (fun s => (J s).inverse)
      (-((J t).inverse.comp (J'.comp (J t).inverse))) t := by
  have hi := Filter.Eventually.self_of_nhds hinv
  have hdiff : DifferentiableAt ℝ (fun s => (J s).inverse) t :=
    ((hi.contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)).comp t
      hJ.differentiableAt
  let Q := deriv (fun s => (J s).inverse) t
  have hprod := hJ.clm_comp hdiff.hasDerivAt
  have heq : (fun s => (J s).comp (J s).inverse) =ᶠ[𝓝 t]
      (fun _ => ContinuousLinearMap.id ℝ E) := by
    filter_upwards [hinv] with s hs
    ext x
    exact hs.self_apply_inverse x
  have hz : J'.comp (J t).inverse + (J t).comp Q = 0 :=
    (hprod.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
  have hQ : Q = -((J t).inverse.comp (J'.comp (J t).inverse)) := by
    ext x
    have hh := congrArg (fun A : E →L[ℝ] E => (J t).inverse (A x)) hz
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      zero_apply, map_add, map_zero, hi.inverse_apply_self] at hh
    simpa only [neg_apply, ContinuousLinearMap.comp_apply] using
      (eq_neg_of_add_eq_zero_right hh)
  exact hQ ▸ hdiff.hasDerivAt

theorem hasDerivAt_jacobi_logarithmicDerivative
    {J V : ℝ → E →L[ℝ] E} {K : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J (V t) t)
    (hV : HasDerivAt V (-(K.comp (J t))) t)
    (hinv : ∀ᶠ s in 𝓝 t, (J s).IsInvertible) :
    HasDerivAt (fun s => (V s).comp (J s).inverse)
      (-(((V t).comp (J t).inverse).comp ((V t).comp (J t).inverse)) - K) t := by
  have hi := Filter.Eventually.self_of_nhds hinv
  convert hV.clm_comp (hasDerivAt_operator_inverse hJ hinv) using 1
  ext x
  simp only [add_apply, sub_apply,
    neg_apply, ContinuousLinearMap.comp_apply, map_neg,
    hi.self_apply_inverse]
  abel

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_jacobi_wronskian
    {J V : ℝ → E →L[ℝ] E} {K : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J (V t) t)
    (hV : HasDerivAt V (-(K.comp (J t))) t)
    (hK : LinearMap.IsSymmetric K.toLinearMap) (u v : E) :
    HasDerivAt (fun s => inner ℝ (J s u) (V s v) - inner ℝ (V s u) (J s v))
      0 t := by
  have hJu : HasDerivAt (fun s => J s u) (V t u) t := by
    simpa using hJ.clm_apply (hasDerivAt_const t u)
  have hJv : HasDerivAt (fun s => J s v) (V t v) t := by
    simpa using hJ.clm_apply (hasDerivAt_const t v)
  have hVu : HasDerivAt (fun s => V s u) (-K (J t u)) t := by
    simpa using hV.clm_apply (hasDerivAt_const t u)
  have hVv : HasDerivAt (fun s => V s v) (-K (J t v)) t := by
    simpa using hV.clm_apply (hasDerivAt_const t v)
  have hz : (inner ℝ (J t u) (-K (J t v)) + inner ℝ (V t u) (V t v)) -
      (inner ℝ (V t u) (V t v) + inner ℝ (-K (J t u)) (J t v)) = 0 := by
    have hk : inner ℝ (K (J t u)) (J t v) = inner ℝ (J t u) (K (J t v)) :=
      hK (J t u) (J t v)
    rw [inner_neg_left, inner_neg_right, hk]
    ring
  exact hz ▸ (hJu.inner ℝ hVv).sub (hVu.inner ℝ hJv)

theorem jacobi_wronskian_eq_zero
    {J V K : ℝ → E →L[ℝ] E} {b t : ℝ}
    (hJ : ∀ s ∈ Set.Icc 0 b, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 b, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 b, LinearMap.IsSymmetric (K s).toLinearMap)
    (hzero : J 0 = 0) (ht : t ∈ Set.Icc 0 b) (u v : E) :
    inner ℝ (J t u) (V t v) - inner ℝ (V t u) (J t v) = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_jacobi_wronskian (hJ s hs) (hV s hs)
      (hK s hs) u v).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (convex_Icc (0 : ℝ) b) h0 ht
  simpa [hzero] using hh

theorem inner_jacobi_eq_time_mul
    {J V K : ℝ → E →L[ℝ] E} {b t : ℝ} (v u : E)
    (hJ : ∀ s ∈ Set.Icc 0 b, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 b, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 b, LinearMap.IsSymmetric (K s).toLinearMap)
    (hKv : ∀ s ∈ Set.Icc 0 b, K s v = 0)
    (hzero : J 0 = 0) (ht : t ∈ Set.Icc 0 b) :
    inner ℝ v (J t u) = t * inner ℝ v (V 0 u) := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hderiv (s : ℝ) (hs : s ∈ Set.Icc 0 b) :
      HasDerivAt (fun r => inner ℝ v (V r u)) 0 s := by
    have hd : HasDerivAt (fun r => V r u) (-K s (J s u)) s := by
      simpa using (hV s hs).clm_apply (hasDerivAt_const s u)
    have hpair : inner ℝ v (K s (J s u)) = 0 := by
      have hk : inner ℝ (K s v) (J s u) = inner ℝ v (K s (J s u)) :=
        hK s hs v (J s u)
      rw [hKv s hs, inner_zero_left] at hk
      exact hk.symm
    simpa only [inner_neg_right, hpair, neg_zero, inner_zero_left, add_zero] using!
      (hasDerivAt_const s v).inner ℝ hd
  have hconst (s : ℝ) (hs : s ∈ Set.Icc 0 b) :
      inner ℝ v (V s u) = inner ℝ v (V 0 u) := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hderiv r hr).hasDerivWithinAt)
      (C := 0) (fun _ _ => by simp) (convex_Icc (0 : ℝ) b) h0 hs
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh
  have hdiff (s : ℝ) (hs : s ∈ Set.Icc 0 b) :
      HasDerivAt (fun r => inner ℝ v (J r u) - r * inner ℝ v (V 0 u)) 0 s := by
    have hd : HasDerivAt (fun r => J r u) (V s u) s := by
      simpa using (hJ s hs).clm_apply (hasDerivAt_const s u)
    simpa only [inner_zero_left, add_zero, one_mul, hconst s hs, sub_self] using!
      ((hasDerivAt_const s v).inner ℝ hd).sub
        ((hasDerivAt_id s).mul_const (inner ℝ v (V 0 u)))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hdiff s hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (convex_Icc (0 : ℝ) b) h0 ht
  exact sub_eq_zero.mp (by simpa [hzero] using hh)

theorem isSymmetric_jacobi_logarithmicDerivative
    [CompleteSpace E]
    {J V K : ℝ → E →L[ℝ] E} {b t : ℝ}
    (hJ : ∀ s ∈ Set.Icc 0 b, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 b, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 b, LinearMap.IsSymmetric (K s).toLinearMap)
    (hzero : J 0 = 0) (ht : t ∈ Set.Icc 0 b) (hinv : (J t).IsInvertible) :
    LinearMap.IsSymmetric ((V t).comp (J t).inverse).toLinearMap := by
  intro x y
  change inner ℝ (V t ((J t).inverse x)) y = inner ℝ x (V t ((J t).inverse y))
  have hw := jacobi_wronskian_eq_zero hJ hV hK hzero ht
    ((J t).inverse x) ((J t).inverse y)
  simpa only [hinv.self_apply_inverse] using (sub_eq_zero.mp hw).symm

end InnerProduct

end PoincareConjecture.RiemannianMetric
