import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.Harnack
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Path.Energy

set_option autoImplicit false

universe u

open Set Filter
open MeasureTheory
open scoped intervalIntegral Manifold ContDiff Bundle

namespace Poincare

namespace RicciFlow.Harnack

theorem integrated_of_finite_origins {t₁ t₂ A B E : ℝ}
    (hfinite : ∀ᶠ T : ℝ in atBot,
      A * (t₁ - T) * E ≤ B * (t₂ - T)) :
    A * E ≤ B := by
  exact Poincare.Asymptotics.ancient_limit_of_scaled_inequality hfinite

theorem integrated_of_finite_start
    {t₁ t₂ A B E : ℝ}
    (finite : ∀ᶠ T : ℝ in atBot,
      A * (t₁ - T) * E ≤ B * (t₂ - T)) :
    A * E ≤ B := by
  exact Poincare.Asymptotics.ancient_limit_of_scaled_inequality finite

theorem integrated_at_terminal_of_finite_origins
    {f q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hqInt : IntervalIntegrable q volume a b)
    (finite : ∀ t ∈ Ioo a b, ∀ᶠ T : ℝ in atBot,
      f a * (a - T) * Real.exp (-(∫ s in a..t, q s) / 2) ≤
        f t * (t - T)) :
    f a * Real.exp (-(∫ s in a..b, q s) / 2) ≤ f b := by
  exact Poincare.Asymptotics.le_at_right_endpoint_of_finite_origins hab hf hqInt finite

theorem integrated_at_terminal_of_finite_origins_flow
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
    (F : PoincareConjecture.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (γ : ℝ → M) {x₁ x₂ : M} (hγa : γ a = x₁) (hγb : γ b = x₂)
    {q : ℝ → ℝ}
    (hscalar : ContinuousOn
      (fun t ↦ (F.connection t).scalarCurvature (γ t)) (Icc a b))
    (hqInt : IntervalIntegrable q volume a b)
    (finite : ∀ t ∈ Ioo a b, ∀ᶠ T : ℝ in atBot,
      (F.connection a).scalarCurvature x₁ * (a - T) *
          Real.exp (-(∫ s in a..t, q s) / 2) ≤
        (F.connection t).scalarCurvature (γ t) * (t - T)) :
    (F.connection a).scalarCurvature x₁ *
        Real.exp (-(∫ s in a..b, q s) / 2) ≤
      (F.connection b).scalarCurvature x₂ := by
  let f : ℝ → ℝ := fun t ↦ (F.connection t).scalarCurvature (γ t)
  have hf : ContinuousOn f (Icc a b) := by
    simpa [f] using hscalar
  have h := Poincare.Asymptotics.le_at_right_endpoint_of_finite_origins
    hab hf hqInt (by
      intro t ht
      simpa [f, hγa] using finite t ht)
  simpa [f, hγa, hγb] using h

theorem integrated_at_terminal_of_finite_origins_flow_of_regular
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
    (hM04 : PoincareConjecture.RicciFlowCurvatureTheory.{u})
    (F : PoincareConjecture.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContinuousOn γ (Icc a b)) {x₁ x₂ : M}
    (hγa : γ a = x₁) (hγb : γ b = x₂)
    (henergy : ContinuousOn
      (fun s ↦ (F.metric s).inner (γ s)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)) (Icc a b))
    (finite : ∀ t ∈ Ioo a b, ∀ᶠ T : ℝ in atBot,
      (F.connection a).scalarCurvature x₁ * (a - T) *
          Real.exp (-(∫ s in a..t,
            (F.metric s).inner (γ s)
              (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)
              (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)) / 2) ≤
        (F.connection t).scalarCurvature (γ t) * (t - T)) :
    (F.connection a).scalarCurvature x₁ *
        Real.exp (-(∫ s in a..b,
          (F.metric s).inner (γ s)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)) / 2) ≤
      (F.connection b).scalarCurvature x₂ := by
  apply integrated_at_terminal_of_finite_origins_flow F hab γ hγa hγb
  · exact Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_path
      hM04 J F γ hJ hγ
  · exact henergy.intervalIntegrable_of_Icc (le_of_lt hab)
  · exact finite

theorem differential_of_finite_origins {Q R t : ℝ}
    (finite : ∀ᶠ T : ℝ in atBot, 0 ≤ Q + R / (t - T)) :
    0 ≤ Q := by
  exact Poincare.Asymptotics.nonneg_of_eventually_add_div_nonneg finite

theorem differential_at_zero_of_finite_origins {q r : ℝ → ℝ}
    (continuous : ContinuousWithinAt q (Iic 0) 0)
    (finite : ∀ t < 0, ∀ᶠ T : ℝ in atBot,
      0 ≤ q t + r t / (t - T)) :
    0 ≤ q 0 := by
  exact Poincare.Asymptotics.nonneg_at_zero_of_finite_origins continuous finite

theorem terminal_nonneg_of_negative
    {f : ℝ → ℝ} (continuous : ContinuousWithinAt f (Iic 0) 0)
    (negative : ∀ t < 0, 0 ≤ f t) :
    0 ≤ f 0 := by
  exact Poincare.Asymptotics.nonneg_at_zero_of_nonneg_neg continuous negative

end RicciFlow.Harnack

end Poincare

namespace Poincare.Geometry.RicciFlow.Harnack

open PoincareConjecture

theorem ancient_differential_of_finite
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hfinite :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ T₀ T₁ : ℝ, T₀ < T₁ →
        ∀ F : RicciFlow n M (Ioo T₀ T₁),
        (∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t)) →
        (∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
        (∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
          ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
        ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
          ∃ dR : ℝ,
            HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
              (Ioo T₀ T₁) t ∧
            dR + (F.connection t).scalarCurvature x / (t - T₀) +
                2 * (mvfderiv (𝓡 n)
                  (fun y ↦ (F.connection t).scalarCurvature y) x) v +
                2 * (F.connection t).ricci x v v ≥ 0)
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hcurv : ∀ t ≤ 0, ∀ x : M,
      LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x)
    (hbound : ∀ t ≤ 0, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) :
    ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR (Iic 0) t ∧
        dR + 2 * (mvfderiv (𝓡 n)
          (fun y ↦ (F.connection t).scalarCurvature y) x) v +
          2 * (F.connection t).ricci x v v ≥ 0 := by
  intro t ht x v
  let d : ℝ → ℝ := fun s ↦
    (F.connection s).laplacian (F.connection s).scalarCurvature x +
      2 * (F.connection s).ricciNormSq x
  let q : ℝ → ℝ := fun s ↦ d s +
    2 * mvfderiv (𝓡 n) (fun y ↦ (F.connection s).scalarCurvature y) x v +
    2 * (F.connection s).ricci x v v
  refine ⟨d t, hM04.scalar_evolution n M (Iic 0) F t ht x, ?_⟩
  have hnegative : ∀ s < 0, 0 ≤ q s := by
    intro s hs
    apply Poincare.Asymptotics.nonneg_of_eventually_add_div_nonneg
      (R := (F.connection s).scalarCurvature x) (t := s)
    filter_upwards [eventually_lt_atBot s] with T hT
    have hT0 : T < 0 := hT.trans hs
    have hsub : Ioo T 0 ⊆ Iic (0 : ℝ) := fun _ h ↦ h.2.le
    have hne : (Ioo T (0 : ℝ)).Nontrivial := by
      refine ⟨T / 2, ⟨by linarith, by linarith⟩, T / 3,
        ⟨by linarith, by linarith⟩, ?_⟩
      linarith
    let G := restrictFlow F hsub inferInstance hne
    obtain ⟨dR, hdR, hineq⟩ := hfinite n M T 0 hT0 G
      (fun r hr ↦ hcomplete r hr.2.le)
      (fun r hr ↦ hcurv r hr.2.le)
      (fun r hr ↦ hbound r hr.2.le) s ⟨hT, hs⟩ x v
    have hid : dR = d s :=
      (hdR.hasDerivAt (Ioo_mem_nhds hT hs)).unique
        ((hM04.scalar_evolution n M (Iic 0) F s hs.le x).hasDerivAt
          (Iic_mem_nhds hs))
    change 0 ≤ dR + (F.connection s).scalarCurvature x / (s - T) +
      2 * mvfderiv (𝓡 n) (fun y ↦ (F.connection s).scalarCurvature y) x v +
      2 * (F.connection s).ricci x v v at hineq
    dsimp only [q]
    linarith
  rcases lt_or_eq_of_le ht with hlt | rfl
  · exact hnegative t hlt
  · have hq : ContinuousOn q (Iic 0) :=
      ((scalarEvolution_continuousOn_ancient hM04 F x).add
        ((scalarCurvature_mvfderiv_continuousOn_time hM04 (Iic 0) F x v).const_mul 2)).add
        ((ricci_continuousOn_ancient F x v v).const_mul 2)
    exact Poincare.Asymptotics.nonneg_at_zero_of_nonneg_neg (hq 0 self_mem_Iic) hnegative

theorem ancient_integrated_of_finite_integrated
    (hM04 : RicciFlowCurvatureTheory.{u})
    (finite_integrated :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ T₀ T₁ t₁ t₂ : ℝ, T₀ < t₁ → t₁ < t₂ → t₂ < T₁ →
        ∀ F : RicciFlow n M (Ioo T₀ T₁),
        (∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t)) →
        (∀ t ∈ Ioo T₀ T₁, ∀ x : M,
          LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
        (∀ t ∈ Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
          ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
        ∀ γ : ℝ → M, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc t₁ t₂) →
        ∀ x₁ x₂ : M, γ t₁ = x₁ → γ t₂ = x₂ →
        (F.connection t₂).scalarCurvature x₂ * (t₂ - T₀) ≥
          (F.connection t₁).scalarCurvature x₁ * (t₁ - T₀) *
            Real.exp (-spacetimeEnergy F γ t₁ t₂ / 2))
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hcurv : ∀ t ≤ 0, ∀ x : M,
      LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x)
    (hbound : ∀ t ≤ 0, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    {t₁ t₂ : ℝ} (ht₁₂ : t₁ < t₂) (ht₂ : t₂ ≤ 0)
    (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc t₁ t₂))
    {x₁ x₂ : M} (hγ₁ : γ t₁ = x₁) (hγ₂ : γ t₂ = x₂) :
    (F.connection t₂).scalarCurvature x₂ ≥
      (F.connection t₁).scalarCurvature x₁ *
        Real.exp (-spacetimeEnergy F γ t₁ t₂ / 2) := by
  apply Poincare.RicciFlow.Harnack.integrated_at_terminal_of_finite_origins_flow
    F ht₁₂ γ hγ₁ hγ₂
  · exact scalarCurvature_continuousOn_path hM04 (Iic 0) F γ
      (fun s hs ↦ le_trans hs.2 ht₂) hγ.continuousOn
  · exact intervalIntegrable_spacetimeEnergy_integrand F ht₁₂
      (fun s hs ↦ le_trans hs.2 ht₂) γ hγ
  intro t ht
  have ht₁ : t₁ < 0 := lt_of_lt_of_le (lt_trans ht.1 ht.2) ht₂
  filter_upwards [eventually_lt_atBot t₁] with T hT
  have hT0 : T < 0 := lt_trans hT ht₁
  have hsub : Ioo T 0 ⊆ Iic (0 : ℝ) := fun s hs ↦ hs.2.le
  have hne : (Ioo T (0 : ℝ)).Nontrivial := by
    refine ⟨T / 2, ⟨by linarith, by linarith⟩, T / 3,
      ⟨by linarith, by linarith⟩, ?_⟩
    linarith
  let G := restrictFlow F hsub inferInstance hne
  have hIcc' : Icc t₁ t ⊆ Icc t₁ t₂ := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 (le_of_lt ht.2)⟩
  have hfin := finite_integrated n M T 0 t₁ t hT ht.1
    (lt_of_lt_of_le ht.2 ht₂) G
    (fun s hs ↦ hcomplete s hs.2.le)
    (fun s hs ↦ hcurv s hs.2.le)
    (fun s hs ↦ hbound s hs.2.le) γ (hγ.mono hIcc') x₁ (γ t) hγ₁ rfl
  dsimp [G, restrictFlow] at hfin
  exact hfin

theorem with_ancient_harnack (hM04 : RicciFlowCurvatureTheory.{u})
    (H : HarnackAncientTheory.{u}) :
    HarnackAncientTheory.{u} :=
  { H with
    ancient_differential := by
      intro n M _ _ _ _ _ _ _ F hcomplete hcurv hbound _
      exact ancient_differential_of_finite hM04 H.finite_differential F
        hcomplete hcurv hbound
    ancient_integrated := by
      intro n M _ _ _ _ _ _ _ F hcomplete hcurv hbound _
      intro t₁ t₂ ht₁₂ ht₂ γ hγ x₁ x₂ hγ₁ hγ₂
      exact ancient_integrated_of_finite_integrated hM04 H.finite_integrated F
        hcomplete hcurv hbound ht₁₂ ht₂ γ hγ hγ₁ hγ₂ }

theorem integrated_of_finite_origins {t₁ t₂ A B E : ℝ}
    (hfinite : ∀ᶠ T : ℝ in Filter.atBot,
      A * (t₁ - T) * E ≤ B * (t₂ - T)) :
    A * E ≤ B := by
  exact Poincare.RicciFlow.Harnack.integrated_of_finite_origins hfinite

theorem integrated_of_finite_start
    {t₁ t₂ A B E : ℝ}
    (finite : ∀ᶠ T : ℝ in Filter.atBot,
      A * (t₁ - T) * E ≤ B * (t₂ - T)) :
    A * E ≤ B := by
  exact Poincare.RicciFlow.Harnack.integrated_of_finite_start finite

theorem differential_of_finite_origins {Q R t : ℝ}
    (finite : ∀ᶠ T : ℝ in Filter.atBot, 0 ≤ Q + R / (t - T)) :
    0 ≤ Q := by
  exact Poincare.RicciFlow.Harnack.differential_of_finite_origins finite

theorem terminal_nonneg_of_negative
    {f : ℝ → ℝ} (continuous : ContinuousWithinAt f (Set.Iic 0) 0)
    (negative : ∀ t < 0, 0 ≤ f t) :
    0 ≤ f 0 := by
  exact Poincare.RicciFlow.Harnack.terminal_nonneg_of_negative continuous negative

end Poincare.Geometry.RicciFlow.Harnack
