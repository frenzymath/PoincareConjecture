import Mathlib.Analysis.Calculus.ImplicitContDiff









set_option autoImplicit false

open scoped ContDiff Topology
open Set Filter

namespace PoincareConjecture.Proofs.M09

variable {P Q R : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]

theorem exists_smooth_implicit (H : P × Q → R) (hH : ContDiff ℝ ∞ H) (u : P × Q)
    (hi : ((fderiv ℝ H u).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible) :
    ∃ (sigma : P → Q) (U : Set P) (W : Set (P × Q)),
      IsOpen U ∧ u.1 ∈ U ∧ IsOpen W ∧ u ∈ W ∧
      sigma u.1 = u.2 ∧ ContDiffOn ℝ ∞ sigma U ∧
      (∀ p ∈ U, (p, sigma p) ∈ W ∧ H (p, sigma p) = H u) ∧
      ∀ z ∈ W, H z = H u ↔ sigma z.1 = z.2 := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hc : ContDiffAt ℝ ∞ H u := hH.contDiffAt
  let sigma := hc.implicitFunction hn hi
  have hsigma : sigma u.1 = u.2 := hc.implicitFunction_apply_self hn hi
  have hsmooth : ContDiffAt ℝ ∞ sigma u.1 := hc.contDiffAt_implicitFunction hn hi
  have hEquation := hc.eventually_apply_implicitFunction hn hi
  have hgraph : Tendsto (fun p ↦ (p, sigma p)) (𝓝 u.1) (𝓝 u) := by
    simpa only [hsigma, id_eq, Prod.mk.eta] using
      (continuousAt_id.prodMk hsmooth.continuousAt).tendsto
  obtain ⟨W, hW, hWopen, huW⟩ :=
    mem_nhds_iff.mp (hc.eventually_apply_eq_iff_implicitFunction hn hi)
  have hD : Continuous (fun z : P × Q ↦
      (fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ P Q)) :=
    (hH.continuous_fderiv hn).clm_comp_const _
  obtain ⟨e, he⟩ := hi
  have hInv : ∀ᶠ z in 𝓝 u,
      ((fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible := by
    have heN : Set.range (fun e : Q ≃L[ℝ] R ↦ (e : Q →L[ℝ] R)) ∈
        𝓝 ((fderiv ℝ H u).comp (ContinuousLinearMap.inr ℝ P Q)) := by
      rw [← he]
      exact e.nhds
    exact hD.continuousAt.preimage_mem_nhds heN
  have hnear : ∀ᶠ p in 𝓝 u.1,
      (p, sigma p) ∈ W ∧ H (p, sigma p) = H u ∧
      ((fderiv ℝ H (p, sigma p)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible :=
    (hgraph.eventually (hWopen.mem_nhds huW)).and
      (hEquation.and (hgraph.eventually hInv))
  obtain ⟨U, hU, hUopen, huU⟩ := mem_nhds_iff.mp hnear
  refine ⟨sigma, U, W, hUopen, huU, hWopen, huW, hsigma, ?_,
    fun p hp ↦ ⟨(hU hp).1, (hU hp).2.1⟩, hW⟩
  apply hUopen.contDiffOn_iff.mpr
  intro p hp
  have hcp : ContDiffAt ℝ ∞ H (p, sigma p) := hH.contDiffAt
  let ip := (hU hp).2.2
  let rho := hcp.implicitFunction hn ip
  have hrho : rho p = sigma p := hcp.implicitFunction_apply_self hn ip
  have hrhos : ContDiffAt ℝ ∞ rho p := hcp.contDiffAt_implicitFunction hn ip
  have hrhog : Tendsto (fun q ↦ (q, rho q)) (𝓝 p) (𝓝 (p, sigma p)) := by
    simpa only [hrho, id_eq] using (continuousAt_id.prodMk hrhos.continuousAt).tendsto
  have heq : sigma =ᶠ[𝓝 p] rho := by
    filter_upwards [hcp.eventually_apply_implicitFunction hn ip,
      hrhog.eventually (hWopen.mem_nhds (hU hp).1)] with q hq hqW
    exact (hW hqW).mp (hq.trans (hU hp).2.1)
  exact hrhos.congr_of_eventuallyEq heq

end PoincareConjecture.Proofs.M09
