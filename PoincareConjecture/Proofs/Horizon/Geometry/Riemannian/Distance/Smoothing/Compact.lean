import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.RegularizedMinimum.Finite
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.FiniteCutoffs
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.FiniteMinimum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Cutoff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem exists_gluing_parameters (k : ℕ) {ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a) :
    ∃ ξ δ : ℝ, 0 < ξ ∧ 0 < δ ∧ ξ + k * δ / 2 ≤ ε ∧
      2 * ξ + 2 * k * δ < a := by
  let ξ := min (ε / 2) (a / 8)
  have hξ : 0 < ξ := lt_min (half_pos hε) (by positivity)
  obtain ⟨δ, hδ, hb⟩ := exists_pos_mul_lt
    (lt_min (half_pos hε) (by positivity : 0 < a / 4)) (2 * ((k : ℝ) + 1))
  have hbε := hb.trans_le (min_le_left _ _)
  have hba := hb.trans_le (min_le_right _ _)
  have hξε : ξ ≤ ε / 2 := min_le_left _ _
  have hξa : ξ ≤ a / 8 := min_le_right _ _
  have hk : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  refine ⟨ξ, δ, hξ, hδ, ?_, ?_⟩ <;> nlinarith

private theorem inactive_of_cutoff_zero (δ : ℝ) (hδ : 0 < δ) (k : ℕ)
    (b ψ : Fin (k + 1) → ℝ) {d ξ a : ℝ}
    (hlow : ∃ j, b j ≤ d + ξ)
    (hhigh : ∀ i, ψ i = 0 → d - ξ + a ≤ b i)
    (hgap : 2 * ξ + 2 * k * δ < a)
    (i : Fin (k + 1)) (hi : ψ i = 0) :
    Poincare.finiteRegularizedMinWeight δ hδ k b i = 0 := by
  obtain ⟨j, hj⟩ := hlow
  apply Poincare.finiteRegularizedMinWeight_eq_zero_of_value_gap
  have hmin := Poincare.finiteRegularizedMin_le δ hδ k b j
  have hlarge := hhigh i hi
  linarith

theorem exists_contMDiff_approx_on_compact_of_local_with_gradient_bound (D : LeviCivitaData g)
    {S : Set M} (hS : IsCompact S) {d : M → ℝ} (hd : ContinuousOn d S)
    {L : M → ℝ} {H : ℝ} (hL : ∀ x ∈ S, 0 ≤ L x)
    (hlocal : ∀ x ∈ S, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ e : ℝ, 0 < e → ∃ f : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧
        (∀ y ∈ U, |f y - d y| ≤ e) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient f y) ≤ L y) ∧
        ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian f y v v ≤ H * g.inner y v v)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      (∀ x ∈ S, |rho x - d x| ≤ ε) ∧
      (∀ x ∈ S, g.tangentNorm x (D.gradient rho x) ≤ L x + η) ∧
      ∀ x ∈ S, ∀ v : TangentSpace (𝓡 n) x,
        D.hessian rho x v v ≤ (H + η) * g.inner x v v := by
  classical
  by_cases hSne : S.Nonempty
  swap
  · refine ⟨fun _ => 0, contMDiff_const, ?_, ?_, ?_⟩ <;>
      intro x hx <;> exact False.elim (hSne ⟨x, hx⟩)
  choose U hU hxU happrox using fun x : S => hlocal x x.property
  obtain ⟨N, c, ψ, θ, hψ, hθ, hψc, hθc, hψb, hθb, hθU, hθone, hψone⟩ :=
    exists_finite_nested_contMDiff_cutoffs (n := n) hS U hU
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hN : 0 < N := by
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨i, -⟩ := hψone x hx
    exact (Nat.zero_le i.val).trans_lt i.isLt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  choose P hP hPbound using fun i =>
    g.exists_metric_derivative_bound_of_hasCompactSupport (hψ i) (hψc i)
  choose B hB hBbound using fun i =>
    D.exists_metric_hessian_bound_of_hasCompactSupport (hψ i) (hψc i)
  let C := ∑ i, (P i + B i)
  have hPC (i : Fin (k + 1)) : P i ≤ C :=
    (le_add_of_nonneg_right (hB i)).trans
      (Finset.single_le_sum (fun j _ => add_nonneg (hP j) (hB j)) (Finset.mem_univ i))
  have hBC (i : Fin (k + 1)) : B i ≤ C :=
    (le_add_of_nonneg_left (hP i)).trans
      (Finset.single_le_sum (fun j _ => add_nonneg (hP j) (hB j)) (Finset.mem_univ i))
  obtain ⟨a, ha, haC⟩ := exists_pos_mul_lt hη C
  have haP (i : Fin (k + 1)) : a * P i ≤ η := by
    have h := mul_le_mul_of_nonneg_right (hPC i) ha.le
    nlinarith
  have haB (i : Fin (k + 1)) : a * B i ≤ η := by
    have h := mul_le_mul_of_nonneg_right (hBC i) ha.le
    nlinarith
  obtain ⟨ξ, δ, hξ, hδ, herror, hgap⟩ := exists_gluing_parameters k hε ha
  choose f hf hferror hfgrad hfH using fun i => happrox (c i) ξ hξ
  obtain ⟨Q, hQ⟩ := hS.bddAbove_image hd
  let b : Fin (k + 1) → M → ℝ := fun i => biasedCutoff (θ i) (ψ i) (f i) Q a
  have hb (i : Fin (k + 1)) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (b i) :=
    contMDiff_biasedCutoff (hU (c i)) (hθ i) (hψ i) (hf i) (hθU i) Q a
  have hbase (i : Fin (k + 1)) (x : M) (hx : x ∈ S) :
      d x - ξ ≤ θ i x * f i x + (1 - θ i x) * Q :=
    cutoff_extension_lower_bound (hθb i) (hθU i) hξ.le (hferror i) (hQ ⟨x, hx, rfl⟩)
  have hblower (i : Fin (k + 1)) (x : M) (hx : x ∈ S) : d x - ξ ≤ b i x := by
    have hbias := mul_nonneg ha.le (sub_nonneg.mpr (hψb i x).2)
    dsimp only [b, biasedCutoff]
    linarith [hbase i x hx]
  have hbhigh (i : Fin (k + 1)) (x : M) (hx : x ∈ S) (hi : ψ i x = 0) :
      d x - ξ + a ≤ b i x := by
    dsimp only [b, biasedCutoff]
    simp only [hi, sub_zero, mul_one]
    linarith [hbase i x hx]
  have hblow (x : M) (hx : x ∈ S) : ∃ i, b i x ≤ d x + ξ := by
    obtain ⟨i, hi⟩ := hψone x hx
    exact ⟨i, biasedCutoff_le_of_inner_eq_one (hθU i) (hθone i) (hferror i)
      hi.self_of_nhds⟩
  let rho : M → ℝ := fun x => Poincare.finiteRegularizedMin δ hδ k (fun i => b i x)
  have hrho : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho := fun x =>
    contMDiffAt_finiteRegularizedMin δ hδ k b (fun i => (hb i).contMDiffAt)
  have hactive (x : M) (hx : x ∈ S) (i : Fin (k + 1))
      (hi : Poincare.finiteRegularizedMinWeight δ hδ k (fun i => b i x) i ≠ 0) :
      ψ i x ≠ 0 := by
    intro hzero
    exact hi (inactive_of_cutoff_zero δ hδ k (fun i => b i x) (fun i => ψ i x)
      (hblow x hx) (fun j hj => hbhigh j x hx hj) hgap i hzero)
  have hbounds (x : M) (hx : x ∈ S) (i : Fin (k + 1))
      (hi : Poincare.finiteRegularizedMinWeight δ hδ k (fun i => b i x) i ≠ 0) :
      g.tangentNorm x (D.gradient (b i) x) ≤ L x + η ∧
      ∀ v : TangentSpace (𝓡 n) x,
        D.hessian (b i) x v v ≤ (H + η) * g.inner x v v := by
    have hxU := mem_of_inner_cutoff_ne_zero (hθU i) (hθone i) (hactive x hx i hi)
    have hbranch := D.biasedCutoff_derivative_bounds_at (Q := Q)
      (hU (c i)) (hθ i) (hψ i) (hf i) (hθU i) (hθone i)
      ha.le (hL x hx) (hP i) (hfgrad i x hxU) (hfH i x hxU)
      (hPbound i x) (hBbound i x) (hactive x hx i hi)
    refine ⟨hbranch.1.trans (add_le_add_right (haP i) (L x)), ?_⟩
    intro v
    apply (hbranch.2 v).trans
    apply mul_le_mul_of_nonneg_right (add_le_add_right (haB i) H)
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  refine ⟨rho, hrho, ?_, ?_, ?_⟩
  · intro x hx
    have hlower := Poincare.sub_le_finiteRegularizedMin δ hδ k (fun i => b i x)
      (fun i => hblower i x hx)
    obtain ⟨i, hi⟩ := hblow x hx
    have hupper := (Poincare.finiteRegularizedMin_le δ hδ k (fun i => b i x) i).trans hi
    have hkδ : 0 ≤ (k : ℝ) * δ / 2 := by positivity
    apply abs_le.mpr
    dsimp only [rho]
    constructor <;> linarith
  · intro x hx
    exact D.gradient_finiteRegularizedMin_norm_le_of_active δ hδ k b
      (fun i => (hb i).contMDiffAt) (add_nonneg (hL x hx) hη.le)
      (fun i hi => (hbounds x hx i hi).1)
  · intro x hx v
    exact D.hessian_finiteRegularizedMin_le_of_active δ hδ k b
      (fun i => (hb i).contMDiffAt) v (fun i hi => (hbounds x hx i hi).2 v)

theorem exists_contMDiff_approx_on_compact_of_local (D : LeviCivitaData g)
    {S : Set M} (hS : IsCompact S) {d : M → ℝ} (hd : ContinuousOn d S)
    {L H : ℝ} (hL : 0 ≤ L)
    (hlocal : ∀ x ∈ S, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ e : ℝ, 0 < e → ∃ f : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧
        (∀ y ∈ U, |f y - d y| ≤ e) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient f y) ≤ L) ∧
        ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian f y v v ≤ H * g.inner y v v)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      (∀ x ∈ S, |rho x - d x| ≤ ε) ∧
      (∀ x ∈ S, g.tangentNorm x (D.gradient rho x) ≤ L + η) ∧
      ∀ x ∈ S, ∀ v : TangentSpace (𝓡 n) x,
        D.hessian rho x v v ≤ (H + η) * g.inner x v v := by
  exact D.exists_contMDiff_approx_on_compact_of_local_with_gradient_bound
    (L := fun _ => L) hS hd (fun _ _ => hL) hlocal hε hη

end PoincareConjecture.LeviCivitaData
