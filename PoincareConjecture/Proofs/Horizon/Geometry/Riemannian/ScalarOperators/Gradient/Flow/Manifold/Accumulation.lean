import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Manifold.Sublevel
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.ScalarDescent
import Mathlib.Analysis.SpecificLimits.Basic











open Set Filter PoincareConjecture
open scoped Topology ContDiff Manifold Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem gradient_energy_nonneg_manifold (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
  by_cases hz : D.gradient f x = 0
  · simp [hz]
  · exact (g.pos x _ hz).le


theorem continuousAt_gradient_energy_manifold (D : LeviCivitaData g)
    {f : M → ℝ} {p : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f p) :
    ContinuousAt (fun x => g.inner x (D.gradient f x) (D.gradient f x)) p := by
  have hG := D.contMDiffAt_gradient hf
  have hi := ((g.contMDiff p).clm_bundle_apply hG).clm_bundle_apply hG
  exact (Bundle.contMDiffAt_totalSpace.mp hi).2.continuousAt



theorem gradient_eq_zero_iff_mfderiv_eq_zero_manifold
    (D : LeviCivitaData g) (f : M → ℝ) (p : M) :
    D.gradient f p = 0 ↔ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 := by
  constructor
  · intro h
    ext v
    have hi := D.inner_gradient f p v
    change g.inner p (D.gradient f p) v = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p v at hi
    simpa [h] using hi.symm
  · intro h
    simp [LeviCivitaData.gradient, mvfderiv, h]


theorem gradient_eq_zero_iff_mvfderiv_eq_zero_manifold
    (D : LeviCivitaData g) (f : M → ℝ) (p : M) :
    D.gradient f p = 0 ↔ mvfderiv (𝓡 n) f p = 0 :=
  gradient_eq_zero_iff_mfderiv_eq_zero_manifold D f p


theorem gradient_energy_eq_zero_iff_mfderiv_eq_zero_manifold
    (D : LeviCivitaData g) (f : M → ℝ) (p : M) :
    g.inner p (D.gradient f p) (D.gradient f p) = 0 ↔
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 := by
  rw [← gradient_eq_zero_iff_mfderiv_eq_zero_manifold D f p]
  constructor
  · intro h
    by_contra hn
    exact (g.pos p _ hn).ne' h
  · intro h
    simp [h]


theorem gradient_energy_eq_zero_iff_mvfderiv_eq_zero_manifold
    (D : LeviCivitaData g) (f : M → ℝ) (p : M) :
    g.inner p (D.gradient f p) (D.gradient f p) = 0 ↔ mvfderiv (𝓡 n) f p = 0 :=
  gradient_energy_eq_zero_iff_mfderiv_eq_zero_manifold D f p


theorem exists_critical_accumulation_of_compact_neg_gradient_manifold
    (D : LeviCivitaData g) {f : M → ℝ} {O K : Set M}
    (hO : IsOpen O) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O)
    (hK : IsCompact K) (hKO : K ⊆ O) {γ : ℝ → M}
    (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hγ : ∀ t, 0 ≤ t → IsMIntegralCurveAt (I := 𝓡 n) γ (fun y => -D.gradient f y) t) :
    ∃ p ∈ K, ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
      Tendsto (γ ∘ τ) atTop (𝓝 p) ∧ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 := by
  have : FirstCountableTopology M := by
    constructor
    intro p
    rw [← (chartAt (EuclideanSpace ℝ (Fin n)) p).symm_map_nhds_eq
      (mem_chart_source _ p)]
    infer_instance
  let a : ℝ → ℝ := fun t => g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t))
  have hdecay (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (f ∘ γ) (-a t) t :=
    hasDerivAt_function_along_neg_gradient_manifold D
      ((hf.contMDiffAt (hO.mem_nhds (hKO (hγK t ht)))).mdifferentiableAt (by simp))
      (hγ t ht)
  obtain ⟨z, hzK, hz⟩ := hK.exists_isMinOn ⟨γ 0, hγK 0 le_rfl⟩
    (hf.continuousOn.mono hKO)
  have hbelow (t : ℝ) (ht : 0 ≤ t) : f z ≤ (f ∘ γ) t := hz (hγK t ht)
  have hsmall (i : ℕ) : ∃ t : ℝ, (i : ℝ) ≤ t ∧ a t < 1 / ((i : ℝ) + 1) :=
    Poincare.ODE.exists_late_small_decay hdecay hbelow (Nat.cast_nonneg i) (by positivity)
  choose τ hτt hτa using hsmall
  have hτ0 (i : ℕ) : 0 ≤ τ i := (Nat.cast_nonneg i).trans (hτt i)
  have hτtop : Tendsto τ atTop atTop :=
    tendsto_atTop_mono hτt tendsto_natCast_atTop_atTop
  have ha0 : Tendsto (a ∘ τ) atTop (𝓝 0) :=
    squeeze_zero (fun i => gradient_energy_nonneg_manifold D f (γ (τ i)))
      (fun i => (hτa i).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hpK, ψ, hψmono, hψ⟩ := hK.tendsto_subseq (fun i => hγK (τ i) (hτ0 i))
  have henergy := continuousAt_gradient_energy_manifold D
    (hf.contMDiffAt (hO.mem_nhds (hKO hpK)))
  have hpenergy : g.inner p (D.gradient f p) (D.gradient f p) = 0 := by
    exact tendsto_nhds_unique (henergy.tendsto.comp hψ) (ha0.comp hψmono.tendsto_atTop)
  have hpgrad : D.gradient f p = 0 := by
    by_contra hne
    exact (g.pos p _ hne).ne' hpenergy
  refine ⟨p, hpK, τ ∘ ψ, hτtop.comp hψmono.tendsto_atTop, ?_, ?_⟩
  · exact hψ
  · ext v
    have hi := D.inner_gradient f p v
    change g.inner p (D.gradient f p) v = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p v at hi
    simpa [hpgrad] using hi.symm


theorem antitoneOn_function_along_neg_gradient_manifold
    (D : LeviCivitaData g) {f : M → ℝ} {O : Set M}
    (hO : IsOpen O) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O)
    {γ : ℝ → M} (hγO : ∀ t, 0 ≤ t → γ t ∈ O)
    (hγ : ∀ t, 0 ≤ t → IsMIntegralCurveAt (I := 𝓡 n) γ (fun y => -D.gradient f y) t) :
    AntitoneOn (f ∘ γ) (Ici 0) := by
  have hd (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_function_along_neg_gradient_manifold D
    ((hf.contMDiffAt (hO.mem_nhds (hγO t ht))).mdifferentiableAt (by simp)) (hγ t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  exact neg_nonpos.mpr (gradient_energy_nonneg_manifold D f _)



theorem exists_limit_of_compact_neg_gradient_of_strict_extrema_manifold
    [T2Space M] (D : LeviCivitaData g) {f : M → ℝ} {O K : Set M}
    (hO : IsOpen O) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hextrema : ∀ p ∈ K, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 →
      (∀ᶠ y in 𝓝 p, y ≠ p → f p < f y) ∨
      (∀ᶠ y in 𝓝 p, y ≠ p → f y < f p))
    {γ : ℝ → M} (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hγ : ∀ t, 0 ≤ t → IsMIntegralCurveAt (I := 𝓡 n) γ (fun y => -D.gradient f y) t) :
    ∃ p ∈ K, Tendsto γ atTop (𝓝 p) ∧ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 ∧
      ((∀ᶠ y in 𝓝 p, y ≠ p → f p < f y) ∨ (∀ᶠ t in atTop, γ t = p)) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨p, hpK, τ, hτ, hlim, hp⟩ :=
    exists_critical_accumulation_of_compact_neg_gradient_manifold D hO hf hK hKO hγK hγ
  have hanti := antitoneOn_function_along_neg_gradient_manifold D hO hf
    (fun t ht => hKO (hγK t ht)) hγ
  have hcont : ContinuousOn γ (Ici 0) :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  rcases hextrema p hpK hp with hmin | hmax
  · exact ⟨p, hpK, Poincare.ODE.tendsto_of_strict_min_accumulation hK
      (hf.continuousOn.mono hKO) hpK hcont hγK hanti hτ hlim hmin, hp, Or.inl hmin⟩
  · have heq := Poincare.ODE.eventually_eq_of_strict_max_accumulation
      (hf.continuousOn.mono hKO) hpK hcont hγK hanti hτ hlim hmax
    exact ⟨p, hpK, tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm), hp, Or.inr heq⟩


theorem tendsto_of_compact_neg_gradient_of_unique_critical_manifold
    [T2Space M] (D : LeviCivitaData g) {f : M → ℝ} {O K : Set M}
    (hO : IsOpen O) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O)
    (hK : IsCompact K) (hKO : K ⊆ O) {p : M}
    (hunique : ∀ y ∈ K, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y = 0 → y = p)
    (hmin : ∀ᶠ y in 𝓝 p, y ≠ p → f p < f y)
    {γ : ℝ → M} (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hγ : ∀ t, 0 ≤ t → IsMIntegralCurveAt (I := 𝓡 n) γ (fun y => -D.gradient f y) t) :
    Tendsto γ atTop (𝓝 p) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨q, hqK, τ, hτ, hlim, hq⟩ :=
    exists_critical_accumulation_of_compact_neg_gradient_manifold D hO hf hK hKO hγK hγ
  obtain rfl := hunique q hqK hq
  exact Poincare.ODE.tendsto_of_strict_min_accumulation hK (hf.continuousOn.mono hKO) hqK
    (fun t ht => (hγ t ht).continuousAt.continuousWithinAt) hγK
    (antitoneOn_function_along_neg_gradient_manifold D hO hf (fun t ht => hKO (hγK t ht)) hγ)
    hτ hlim hmin



theorem exists_strict_minimum_limit_of_compact_neg_gradient_manifold
    [T2Space M] (D : LeviCivitaData g) {f : M → ℝ} {O K : Set M}
    (hO : IsOpen O) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O)
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hextrema : ∀ p ∈ K, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 →
      (∀ᶠ y in 𝓝 p, y ≠ p → f p < f y) ∨
      (∀ᶠ y in 𝓝 p, y ≠ p → f y < f p))
    {γ : ℝ → M} (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hγ : ∀ t, 0 ≤ t → IsMIntegralCurveAt (I := 𝓡 n) γ (fun y => -D.gradient f y) t)
    (hregular : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (γ 0) ≠ 0) :
    ∃ p ∈ K, Tendsto γ atTop (𝓝 p) ∧ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0 ∧
      ∀ᶠ y in 𝓝 p, y ≠ p → f p < f y := by
  obtain ⟨p, hpK, hlim, hp, hcase⟩ :=
    exists_limit_of_compact_neg_gradient_of_strict_extrema_manifold D hO hf hK hKO
      hextrema hγK hγ
  refine ⟨p, hpK, hlim, hp, ?_⟩
  rcases hcase with hmin | hstationary
  · exact hmin
  · have hgrad := (gradient_eq_zero_iff_mfderiv_eq_zero_manifold D f p).mpr hp
    obtain ⟨a, hγa, ha⟩ := (hstationary.and (eventually_gt_atTop 0)).exists
    have hfield : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1
        (T% (fun y => -D.gradient f y)) O := by
      intro y hy
      exact ((D.contMDiffAt_gradient (hf.contMDiffAt (hO.mem_nhds hy))).neg_section.of_le
        (show (1 : ℕ∞ω) ≤ ∞ by simp)).contMDiffWithinAt
    have hconst : IsMIntegralCurveOn (I := 𝓡 n) (fun _ => p)
        (fun y => -D.gradient f y) (Ioi 0) := by
      intro t ht
      simpa only [hgrad, neg_zero, ContinuousLinearMap.smulRight_zero] using
        (hasMFDerivWithinAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n) p (Ioi 0) t)
    have heq := Poincare.Manifold.eqOn_of_isMIntegralCurveOn hO hfield
      isOpen_Ioi (convex_Ioi (0 : ℝ)).isPreconnected ha
      (fun t (ht : 0 < t) => hKO (hγK t ht.le))
      (IsMIntegralCurveAt.isMIntegralCurveOn (fun t (ht : 0 < t) => hγ t ht.le))
      hconst hγa
    have hlimp : Tendsto γ (𝓝[>] 0) (𝓝 p) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (heq ht).symm
    have hγ0 : γ 0 = p := tendsto_nhds_unique
      ((hγ 0 le_rfl).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlimp
    exact (hregular (hγ0 ▸ hp)).elim

end Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
