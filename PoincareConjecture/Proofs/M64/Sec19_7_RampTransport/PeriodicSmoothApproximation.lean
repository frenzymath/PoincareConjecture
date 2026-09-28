import PoincareConjecture.Proofs.M63.Mathlib.PeriodicRetractionApproximation
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding











set_option autoImplicit false
set_option warningAsError true

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]





theorem exists_periodic_smooth_approximation_in_open_jets
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U)
    (hre : ∀ p, rho (e p) = p)
    {period : ℝ} (hperiod : 0 < period) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hp : Function.Periodic gamma period)
    {O : Set (W × W × W)} (hO : IsOpen O)
    (hjet : ∀ x, ((e ∘ gamma) x, deriv (e ∘ gamma) x,
      deriv (deriv (e ∘ gamma)) x) ∈ O)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ sigma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ sigma ∧
      Function.Periodic sigma period ∧
      (∀ x, ((e ∘ sigma) x, deriv (e ∘ sigma) x,
        deriv (deriv (e ∘ sigma)) x) ∈ O) ∧
      ∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < epsilon := by
  let c := e ∘ gamma
  have hc : ContDiff ℝ 2 c :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hcp : Function.Periodic c period := hp.comp e
  have hc1 : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hp1 := hcp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hp2 := hp1.deriv_of_differentiable (hc1.differentiable (by norm_num))
  let jet := fun x => (c x, deriv c x, deriv (deriv c) x)
  have hjetp : Function.Periodic jet period := by
    intro x
    dsimp only [jet]
    rw [hcp x, hp1 x, hp2 x]
  have hjetc : Continuous jet :=
    hc.continuous.prodMk (hc1.continuous.prodMk hc1.continuous_deriv_one)
  have hcompact : IsCompact (range jet) :=
    hjetp.compact_of_continuous hperiod.ne' hjetc
  have hsub : range jet ⊆ O := by
    rintro _ ⟨x, rfl⟩
    exact hjet x
  obtain ⟨eta, heta, hthick⟩ := hcompact.exists_thickening_subset_open hO hsub
  let tolerance := min epsilon (eta / 2)
  have htolerance : 0 < tolerance := lt_min hepsilon (half_pos heta)
  have htol_eta : tolerance < eta :=
    (min_le_right _ _).trans_lt (half_lt_self heta)
  have hP : ContDiffOn ℝ ∞ (e ∘ rho) U :=
    (M63.smooth_retraction_differentials he hU heU hrho hre).1
  have hPU : MapsTo (e ∘ rho) U U := fun z _ => heU (mem_range_self (rho z))
  have hPP (z : W) (_hz : z ∈ U) : (e ∘ rho) ((e ∘ rho) z) = (e ∘ rho) z := by
    simp only [Function.comp_apply, hre]
  have hcU : range c ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact heU (mem_range_self (gamma x))
  have hfix (x : ℝ) : (e ∘ rho) (c x) = c x := by
    simp only [Function.comp_apply, c, hre]
  obtain ⟨q, hq, hqp, hqfix, hnear⟩ :=
    M63.exists_periodic_smooth_fixed_C2_approximation
      hU hP hPU hPP hperiod hc hcp hcU hfix htolerance
  let sigma := rho ∘ q
  have hsigma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ sigma :=
    hrho.comp_contMDiff hq.contMDiff (fun x => (hqfix x).1)
  have heq : e ∘ sigma = q := funext fun x => (hqfix x).2
  refine ⟨sigma, hsigma, hqp.comp rho, ?_, ?_⟩
  · intro x
    rw [heq]
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨jet x, mem_range_self x, ?_⟩
    rw [dist_eq_norm]
    exact (max_le (hnear x).1.le
      (max_le (hnear x).2.1.le (hnear x).2.2.le)).trans_lt htol_eta
  · intro x
    rw [heq]
    exact ⟨(hnear x).1.trans_le (min_le_left _ _),
      (hnear x).2.1.trans_le (min_le_left _ _),
      (hnear x).2.2.trans_le (min_le_left _ _)⟩





theorem exists_compact_periodic_smooth_approximation
    [T2Space M] [CompactSpace M] [Nonempty M] :
    ∃ (dimension : ℕ) (e : M → EuclideanSpace ℝ (Fin dimension)),
      ContMDiff (𝓡 n) (𝓡 dimension) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ (period : ℝ), 0 < period → ∀ gamma : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma → Function.Periodic gamma period →
        ∀ epsilon : ℝ, 0 < epsilon →
        ∃ sigma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ sigma ∧
          Function.Periodic sigma period ∧
          ∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < epsilon ∧
            ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < epsilon ∧
            ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < epsilon := by
  obtain ⟨dimension, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hre, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  refine ⟨dimension, e, he, hemb, ?_⟩
  intro period hperiod gamma hgamma hp epsilon hepsilon
  obtain ⟨sigma, hsigma, hsper, _hjet, hnear⟩ :=
    exists_periodic_smooth_approximation_in_open_jets he hU heU hrho hre
      hperiod hgamma hp isOpen_univ (fun _ => mem_univ _) hepsilon
  exact ⟨sigma, hsigma, hsper, hnear⟩

end PoincareConjecture.M64.RampTransport
