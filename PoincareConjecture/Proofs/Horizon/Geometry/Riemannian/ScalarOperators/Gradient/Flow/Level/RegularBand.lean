import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.CompactBand
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Manifold.Accumulation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompactHessian

noncomputable section

open Set Filter PoincareConjecture
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
omit [T3Space M] in

theorem exists_gradient_lower_bound_on_compact_regular_set
    (D : LeviCivitaData g) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {K : Set M} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ l : ℝ, 0 < l ∧ ∀ x ∈ K, l ≤ g.tangentNorm x (D.gradient f x) := by
  have henergy : Continuous (fun x => g.inner x (D.gradient f x) (D.gradient f x)) :=
    continuous_iff_continuousAt.mpr (fun x => continuousAt_gradient_energy_manifold D (hf x))
  have hnorm : Continuous (fun x => g.tangentNorm x (D.gradient f x)) :=
    Real.continuous_sqrt.comp henergy
  have hpos (x : M) (hx : x ∈ K) : 0 < g.tangentNorm x (D.gradient f x) := by
    apply Real.sqrt_pos.mpr
    exact g.pos x _ (fun hz =>
      hreg x hx ((gradient_eq_zero_iff_mfderiv_eq_zero_manifold D f x).mp hz))
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · exact ⟨1, zero_lt_one, by simp [hKe]⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKn hnorm.continuousOn
    exact ⟨g.tangentNorm x (D.gradient f x), hpos x hx, hmin⟩

theorem exists_normalizedGradient_flow_on_compact_regular_band
    (D : LeviCivitaData g) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {U : Set M} (hU : IsOpen U)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b : ℝ} (hband : IsCompact {x | x ∈ U ∧ f x ∈ Icc a b})
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    {T : ℝ} (hT : 0 ≤ T)
    (hlower : ∀ x ∈ K, a ≤ f x) (hupper : ∀ x ∈ K, f x + T ≤ b) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (-δ) (T + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) (T + δ), Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y))
          (D.normalizedGradient f) (Ioo (-δ) (T + δ))) ∧
      ∀ y ∈ V, ∀ t ∈ Icc 0 T, f (Φ (t, y)) = f y + t := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let B : Set M := {x | x ∈ U ∧ f x ∈ Icc a b}
  obtain ⟨L, hL, hBL, hLU⟩ := exists_compact_between hband hU (show B ⊆ U from fun _ h => h.1)
  obtain ⟨l, hl, hgrad⟩ := D.exists_gradient_lower_bound_on_compact_regular_set
    hf hL (fun x hx => hreg x (hLU hx))
  obtain ⟨H, hH, hhess⟩ := D.exists_metric_hessian_bound_on_compact hf hL
  have hKB : K ⊆ B := by
    intro x hx
    exact ⟨hKU hx, hlower x hx, by linarith [hupper x hx]⟩
  have heq : {x | x ∈ interior L ∧ f x ∈ Icc a b} = B := by
    ext x
    exact ⟨fun hx => ⟨hLU (interior_subset hx.1), hx.2⟩,
      fun hx => ⟨hBL hx, hx.2⟩⟩
  obtain ⟨V, δ, Φ, hV, hKV, hVL, hδ, hΦ, hinit, horbit, hlevel⟩ :=
    D.exists_uniform_normalizedGradient_manifoldFlow_on_compact_band
      isOpen_interior hf.contMDiffOn hl hH
      (fun y hy => hgrad y (interior_subset hy))
      (fun y hy v _ => (le_abs_self _).trans (hhess y (interior_subset hy) v))
      (heq.symm ▸ hband) hK (hKB.trans hBL) hT hlower hupper
  exact ⟨V, δ, Φ, hV, hKV, hVL.trans (interior_subset.trans hLU), hδ, hΦ, hinit,
    fun y hy => ⟨fun t ht => hLU (interior_subset ((horbit y hy).1 t ht)), (horbit y hy).2⟩,
    fun y hy t ht => (hlevel y hy t ht).1⟩
end PoincareConjecture.LeviCivitaData
