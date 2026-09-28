import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Strong







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal ContDiff

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_integral_partial_sub_sq_of_eventually_weak_divergence
    {O U : Set E} (hO : IsOpen O) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hclUO : closure U ⊆ O)
    [IsFiniteMeasure (volume.restrict O)] [IsFiniteMeasure (volume.restrict U)]
    {u : ℕ → E → ℝ} {v : E → ℝ}
    {F : ℕ → Fin d → E → ℝ} {f : ℕ → E → ℝ}
    {A : ℕ → E → Fin d → Fin d → ℝ} {B : E → Fin d → Fin d → ℝ}
    {L : ℝ≥0} {c C D : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlim : TendstoUniformlyOn u v atTop O) (hAlim : TendstoUniformlyOn A B atTop O)
    (hdata : ∀ᶠ k in atTop,
      LipschitzOnWith L (u k) O ∧
      (∀ i, MemLp (F k i) 2 (volume.restrict O)) ∧
      MemLp (f k) 2 (volume.restrict O) ∧
      (∀ x ∈ O, |f k x| ≤ C) ∧ (∀ i x, x ∈ O → |F k i x| ≤ C) ∧
      (∀ x ∈ O, ∀ w : Fin d → ℝ,
        c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j, A k x i j * w j * w i) ∧
      (∀ x ∈ O, ∀ i, F k i x =
        -(∑ j, A k x i j * fderiv ℝ (u k) x (EuclideanSpace.single j 1))) ∧
      (∀ (ψ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
        (∫ x in O, ∑ i, F k i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
          ∫ x in O, f k x * ψ x))
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hφU : ∀ x ∈ U, φ x = 1)
    (hdφ : ∀ i x, x ∈ O → |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ D)
    (i : Fin d) :
    Tendsto (fun k => ∫ x in U,
      (fderiv ℝ (u k) x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdata
  have htail (k : ℕ) := hN (k + N) (Nat.le_add_left N k)
  have hlimN := hlim.seq_tendstoUniformlyOn (fun k => k + N) (tendsto_add_atTop_nat N)
  have hAN := hAlim.seq_tendstoUniformlyOn (fun k => k + N) (tendsto_add_atTop_nat N)
  have hu := fun k => (htail k).1
  have hv := lipschitzOnWith_of_tendstoUniformlyOn hu hlimN
  have hstrong := tendsto_lipschitzPartialL2_of_weak_divergence
    hO hU hUc hclUO hc hC hD hu hlimN hAN.uniformCauchySeqOn
    (fun k => (htail k).2.1) (fun k => (htail k).2.2.1)
    (fun k => (htail k).2.2.2.1) (fun k => (htail k).2.2.2.2.1)
    (fun k => (htail k).2.2.2.2.2.1) (fun k => (htail k).2.2.2.2.2.2.1)
    (fun k => (htail k).2.2.2.2.2.2.2) hφ hφc hφO hφ0 hφ1 hφU hdφ i
  have hUO : U ⊆ O := subset_closure.trans hclUO
  have hnorm := ((hstrong.sub (tendsto_const_nhds
    (x := lipschitzPartialL2 hU (hv.mono hUO) i))).norm).pow 2
  apply (tendsto_add_atTop_iff_nat N).mp
  convert hnorm using 1
  · funext k
    exact (norm_toLp_sub_sq_eq_integral
      ((Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
        hU ((hu k).mono hUO) (EuclideanSpace.single i 1)).mono_exponent le_top)
      ((Poincare.Analysis.Sobolev.Weak.memLp_top_fderiv_apply_of_lipschitzOn
        hU (hv.mono hUO) (EuclideanSpace.single i 1)).mono_exponent le_top)).symm
  · simp

end Poincare.Analysis.Elliptic
