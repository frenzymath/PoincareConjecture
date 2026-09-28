import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Pullback











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace PoincareConjecture.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000 in




theorem terminalCurvature_eventually_moving_pullback_jet_error
    {U V : Set E₃} (hU : IsOpen U) (hV : IsOpen V)
    {B : ℕ → E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ}
    {B₀ : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ}
    {a : ℕ → E₃ → E₃} {a₀ : E₃ → E₃}
    (hB₀ : ContDiffOn ℝ ∞ B₀ U) (ha₀ : ContDiffOn ℝ ∞ a₀ V)
    (haU : MapsTo a₀ V U)
    (hBlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) W)
    (halocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W)
    (hBjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (B k)) (iteratedFDeriv ℝ m B₀) atTop K)
    (hajet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m a₀) atTop K)
    {m : ℕ} {K : Set E₃} (hK : IsCompact K) (hKV : K ⊆ V)
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      dist
        (iteratedFDeriv ℝ m (fun y =>
          (B k (a k y)).bilinearComp (fderiv ℝ (a k) y)
            (fderiv ℝ (a k) y)) x)
        (iteratedFDeriv ℝ m (fun y =>
          (B₀ (a₀ y)).bilinearComp (fderiv ℝ a₀ y)
            (fderiv ℝ a₀ y)) x) < rho := by
  obtain ⟨_, hpull⟩ := Poincare.Analysis.Calculus.smooth_convergence_pullback_bilinear_on_open
    hU hV hB₀ ha₀ haU hBlocal halocal hBjet hajet
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hpull m K hK hKV)) rho hrho]
    with k hk x hx
  simpa only [dist_comm] using hk x hx

end PoincareConjecture.M47
