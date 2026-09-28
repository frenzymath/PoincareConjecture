import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Local
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Metric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Extrema

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology BigOperators

namespace Poincare.Riemannian.RadialTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiffAt_covariantDerivative
    {Γ : E → E →L[ℝ] F →L[ℝ] F} {Y : E → F} {x : E}
    (hΓ : ContDiffAt ℝ ∞ Γ x) (hY : ContDiffAt ℝ ∞ Y x) (u : E) :
    ContDiffAt ℝ ∞ (fun z => covariantDerivative Γ Y z u) x := by
  exact ((hY.fderiv_right (by simp)).clm_apply contDiffAt_const).add
    ((hΓ.clm_apply contDiffAt_const).clm_apply hY)

lemma fderiv_metric_pairing
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {Y Z : E → F} {x : E}
    (hG : DifferentiableAt ℝ G x) (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x)
    (hcompat : ∀ u : E, ∀ a b : F,
      fderiv ℝ (fun z => G z a b) x u =
        G x (Γ x u a) b + G x a (Γ x u b)) (u : E) :
    fderiv ℝ (fun z => G z (Y z) (Z z)) x u =
      G x (covariantDerivative Γ Y x u) (Z x) +
        G x (Y x) (covariantDerivative Γ Z x u) := by
  have hd := (hG.hasFDerivAt.clm_apply hY.hasFDerivAt).clm_apply hZ.hasFDerivAt
  have heq := congrArg (fun L => L u) hd.fderiv
  have hc : fderiv ℝ G x u (Y x) (Z x) =
      G x (Γ x u (Y x)) (Z x) + G x (Y x) (Γ x u (Z x)) := by
    rw [← metric_fderiv_apply hG]
    exact hcompat u _ _
  rw [heq]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, covariantDerivative, map_add, hc]
  ring

lemma second_fderiv_metric_pairing_of_zero_jets
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {Y Z : E → F} {O : Set E}
    (hO : IsOpen O) (hzero : (0 : E) ∈ O)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hY : ContDiffOn ℝ ∞ Y O) (hZ : ContDiffOn ℝ ∞ Z O)
    (hcompat : ∀ x ∈ O, ∀ u : E, ∀ a b : F,
      fderiv ℝ (fun z => G z a b) x u =
        G x (Γ x u a) b + G x a (Γ x u b)) (u : E)
    (hfirst : covariantDerivative Γ Y 0 u = 0)
    (hsecond : covariantDerivative Γ (fun x => covariantDerivative Γ Y x u) 0 u = 0) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => G z (Y z) (Z z)) x u) 0 u =
      G 0 (Y 0) (covariantDerivative Γ (fun x => covariantDerivative Γ Z x u) 0 u) := by
  have hΓ0 := hΓ.contDiffAt (hO.mem_nhds hzero)
  have hG0 := hG.contDiffAt (hO.mem_nhds hzero)
  have hY0 := hY.contDiffAt (hO.mem_nhds hzero)
  have hZ0 := hZ.contDiffAt (hO.mem_nhds hzero)
  have hDY := contDiffAt_covariantDerivative hΓ0 hY0 u
  have hDZ := contDiffAt_covariantDerivative hΓ0 hZ0 u
  have heq : (fun x => fderiv ℝ (fun z => G z (Y z) (Z z)) x u) =ᶠ[𝓝 0]
      (fun x => G x (covariantDerivative Γ Y x u) (Z x) +
        G x (Y x) (covariantDerivative Γ Z x u)) := by
    filter_upwards [hO.mem_nhds hzero] with x hx
    exact fderiv_metric_pairing
      ((hG.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      ((hY.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      ((hZ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      (hcompat x hx) u
  rw [heq.fderiv_eq]
  rw [fderiv_fun_add
    (((hG0.clm_apply hDY).clm_apply hZ0).differentiableAt (by simp))
    (((hG0.clm_apply hY0).clm_apply hDZ).differentiableAt (by simp))]
  simp only [add_apply]
  rw [fderiv_metric_pairing (hG0.differentiableAt (by simp))
    (hDY.differentiableAt (by simp)) (hZ0.differentiableAt (by simp)) (hcompat 0 hzero),
    fderiv_metric_pairing (hG0.differentiableAt (by simp))
      (hY0.differentiableAt (by simp)) (hDZ.differentiableAt (by simp)) (hcompat 0 hzero)]
  simp only [hfirst, hsecond, map_zero, zero_apply, zero_add, add_zero]

lemma second_fderiv_nonpos_of_isLocalMax
    {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hzero : (0 : E) ∈ O)
    (hf : ContDiffOn ℝ ∞ f O) (hmax : IsLocalMax f 0) (u : E) :
    fderiv ℝ (fun x => fderiv ℝ f x u) 0 u ≤ 0 := by
  have hf0 := hf.contDiffAt (hO.mem_nhds hzero)
  have hray : Continuous (fun t : ℝ => t • u) := continuous_id.smul continuous_const
  have htend : Tendsto (fun t : ℝ => t • u) (𝓝 (0 : ℝ)) (𝓝 (0 : E)) := by
    simpa only [zero_smul] using
      (hray.continuousAt : ContinuousAt (fun t : ℝ => t • u) 0).tendsto
  have hφmax : IsLocalMax (fun t : ℝ => f (t • u)) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, f (t • u) ≤ f ((0 : ℝ) • u)
    simpa only [zero_smul] using htend.eventually hmax
  have hφcont : ContinuousAt (fun t : ℝ => f (t • u)) 0 := by
    change Tendsto (fun t : ℝ => f (t • u)) (𝓝 0) (𝓝 (f ((0 : ℝ) • u)))
    simpa only [zero_smul, Function.comp_def] using hf0.continuousAt.tendsto.comp htend
  have hder : deriv (fun t : ℝ => f (t • u)) =ᶠ[𝓝 0]
      (fun t => fderiv ℝ f (t • u) u) := by
    have hev : ∀ᶠ t : ℝ in 𝓝 0, t • u ∈ O := by
      exact htend.eventually (hO.mem_nhds hzero)
    filter_upwards [hev] with t ht
    have h := ((hf.contDiffAt (hO.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt t ((hasDerivAt_id t).smul_const u)
    simpa only [Function.comp_def, id_eq, one_smul] using h.deriv
  have hdf : ContDiffAt ℝ ∞ (fun x => fderiv ℝ f x u) 0 :=
    (hf0.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hdf' : HasFDerivAt (fun x => fderiv ℝ f x u)
      (fderiv ℝ (fun x => fderiv ℝ f x u) 0) ((0 : ℝ) • u) := by
    simpa only [zero_smul] using (hdf.differentiableAt (by simp)).hasFDerivAt
  have hdd := hdf'.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const u)
  have heq : deriv (deriv (fun t : ℝ => f (t • u))) 0 =
      fderiv ℝ (fun x => fderiv ℝ f x u) 0 u := by
    rw [hder.deriv_eq]
    simpa only [Function.comp_def, id_eq, one_smul, zero_smul] using hdd.deriv
  rw [← heq]
  exact PoincareConjecture.LeviCivitaData.deriv_deriv_nonpos_of_isLocalMax hφmax hφcont

def coordinateRoughLaplacian {ι : Type*} [Fintype ι]
    (Γ : E → E →L[ℝ] F →L[ℝ] F) (S : E → F)
    (e : ι → E) (b x : E) : F :=
  (∑ i, covariantDerivative Γ (fun z => covariantDerivative Γ S z (e i)) x (e i)) -
    covariantDerivative Γ S x b

lemma metric_roughLaplacian_nonpos_of_zero_jets
    {ι : Type*} [Fintype ι]
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {N S : E → F} {O : Set E}
    (hO : IsOpen O) (hzero : (0 : E) ∈ O)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hN : ContDiffOn ℝ ∞ N O) (hS : ContDiffOn ℝ ∞ S O)
    (hcompat : ∀ x ∈ O, ∀ u : E, ∀ a b : F,
      fderiv ℝ (fun z => G z a b) x u =
        G x (Γ x u a) b + G x a (Γ x u b))
    (hfirst : ∀ u, covariantDerivative Γ N 0 u = 0)
    (hsecond : ∀ u,
      covariantDerivative Γ (fun x => covariantDerivative Γ N x u) 0 u = 0)
    (hmax : IsLocalMax (fun x => G x (N x) (S x)) 0)
    (e : ι → E) (b : E) :
    G 0 (N 0) (coordinateRoughLaplacian Γ S e b 0) ≤ 0 := by
  have hf : ContDiffOn ℝ ∞ (fun x => G x (N x) (S x)) O :=
    (hG.clm_apply hN).clm_apply hS
  have hd (u : E) : G 0 (N 0) (covariantDerivative Γ S 0 u) = 0 := by
    have hh := fderiv_metric_pairing
      ((hG.contDiffAt (hO.mem_nhds hzero)).differentiableAt (by simp))
      ((hN.contDiffAt (hO.mem_nhds hzero)).differentiableAt (by simp))
      ((hS.contDiffAt (hO.mem_nhds hzero)).differentiableAt (by simp))
      (hcompat 0 hzero) u
    simpa only [hmax.fderiv_eq_zero, zero_apply, hfirst, map_zero, zero_add] using hh.symm
  have hdd (u : E) :
      G 0 (N 0) (covariantDerivative Γ (fun x => covariantDerivative Γ S x u) 0 u) ≤ 0 := by
    rw [← second_fderiv_metric_pairing_of_zero_jets hO hzero hΓ hG hN hS
      hcompat u (hfirst u) (hsecond u)]
    exact second_fderiv_nonpos_of_isLocalMax hO hzero hf hmax u
  simp only [coordinateRoughLaplacian, map_sub, map_sum, hd, sub_zero]
  exact Finset.sum_nonpos fun i _ => hdd (e i)

variable [FiniteDimensional ℝ E] [CompleteSpace F]

theorem exists_supporting_contact_roughLaplacian_nonpos
    {ι : Type*} [Fintype ι]
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {S : E → F} {O : Set E}
    (hO : IsOpen O) (hzero : (0 : E) ∈ O)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hS : ContDiffOn ℝ ∞ S O)
    (hcompat : ∀ x ∈ O, ∀ u : E, ∀ a b : F,
      fderiv ℝ (fun z => G z a b) x u =
        G x (Γ x u a) b + G x a (Γ x u b))
    (n p : F) (e : ι → E) (b : E) :
    ∃ (r : ℝ) (N P : E → F), 0 < r ∧ ball 0 r ⊆ O ∧
      ContDiff ℝ ∞ N ∧ ContDiff ℝ ∞ P ∧ N 0 = n ∧ P 0 = p ∧
      (∀ u ∈ ball 0 r, ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => N (s • u)) (-(Γ (t • u) u (N (t • u)))) t) ∧
      (∀ u ∈ ball 0 r, ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => P (s • u)) (-(Γ (t • u) u (P (t • u)))) t) ∧
      (IsLocalMax (fun x => G x (N x) (S x - P x)) 0 →
        G 0 n (coordinateRoughLaplacian Γ S e b 0) ≤ 0) := by
  obtain ⟨rN, N, hrN, hNO, hN, hN0, hNeq, hNfirst, hNsecond⟩ :=
    exists_field_local hO hzero hΓ n
  obtain ⟨rP, P, hrP, hPO, hP, hP0, hPeq, _, _⟩ :=
    exists_field_local hO hzero hΓ p
  let r := min rN rP
  have hr : 0 < r := lt_min hrN hrP
  have hrN' : ball (0 : E) r ⊆ ball 0 rN := ball_subset_ball (min_le_left _ _)
  have hrP' : ball (0 : E) r ⊆ ball 0 rP := ball_subset_ball (min_le_right _ _)
  refine ⟨r, N, P, hr, hrN'.trans hNO, hN, hP, hN0, hP0,
    fun u hu => hNeq u (hrN' hu), fun u hu => hPeq u (hrP' hu), ?_⟩
  intro hmax
  have hpair : ∀ x ∈ ball (0 : E) r, G x (N x) (P x) = G 0 n p := by
    intro x hx
    have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • x ∈ O := by
      apply hNO
      apply hrN'
      rw [mem_ball, dist_zero_right] at hx ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx
    have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [ht.1], ht.2⟩
    simpa only [hN0, hP0] using fields_metric_eq_of_radial_parallel hO
      (hG.differentiableOn (by simp)) hcompat x hseg N P
      (fun t ht => hNeq x (hrN' hx) t (htime t ht))
      (fun t ht => hPeq x (hrP' hx) t (htime t ht))
  have hmax' : IsLocalMax (fun x => G x (N x) (S x)) 0 := by
    filter_upwards [hmax, isOpen_ball.mem_nhds (mem_ball_self hr)] with x hx hxball
    have hh := hpair x hxball
    have hx' : G x (N x) (S x) - G x (N x) (P x) ≤
        G 0 n (S 0) - G 0 n p := by
      simpa only [map_sub, hN0, hP0] using hx
    rw [hh] at hx'
    rw [hN0]
    linarith
  rw [← hN0]
  exact metric_roughLaplacian_nonpos_of_zero_jets hO hzero hΓ hG hN.contDiffOn
    hS hcompat hNfirst hNsecond hmax' e b

end Poincare.Riemannian.RadialTransport
