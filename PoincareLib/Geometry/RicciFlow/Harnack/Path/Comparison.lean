import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Harnack
import PoincareLib.Geometry.RicciFlow.Harnack.Ancient
import PoincareLib.Geometry.RicciFlow.Harnack.MetricTransport
import PoincareLib.Geometry.RicciFlow.Harnack.Path.Energy
import PoincareLib.Geometry.RicciFlow.Harnack.Path.Scalar
import PoincareLib.Geometry.Curvature.Operator.RicciBounds

/-!
# Integrating Harnack inequalities along C1 paths

These applications supply the scalar comparison and ancient terminal consumers
with regularity proved from the flow and path. The differential or finite-origin
Harnack estimate is the remaining geometric input.
Source: Morgan--Tian (2007), Theorem 4.37 and Corollary 4.39, p. 81;
Theorem 4.40, p. 82.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace Poincare.Geometry.RicciFlow.Harnack

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}

theorem spacetime_path_energy_calculus
    (hM04 : PoincareMT.RicciFlowCurvatureTheory.{u})
    (F : PoincareMT.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b)) :
    IntervalIntegrable (fun t ↦ (F.metric t).inner (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) volume a b ∧
    ContinuousOn (fun t ↦ (F.connection t).scalarCurvature (γ t)) (Icc a b) ∧
    ∀ t ∈ Ioo a b,
      HasDerivAt (fun s ↦ (F.connection s).scalarCurvature (γ s))
        (deriv (fun s ↦ (F.connection s).scalarCurvature (γ t)) t +
          mvfderiv (𝓡 n) (F.connection t).scalarCurvature (γ t)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)) t := by
  refine ⟨intervalIntegrable_spacetimeEnergy_integrand F hab hJ γ hγ,
    scalarCurvature_continuousOn_path hM04 J F γ hJ hγ.continuousOn, ?_⟩
  intro t ht
  exact scalarCurvature_hasDerivAt_path hM04 F hJ γ hγ ht

theorem finite_integrated_of_path_differential
    (hM04 : PoincareMT.RicciFlowCurvatureTheory.{u})
    (F : PoincareMT.RicciFlow n M J) {T a b : ℝ} (hTa : T < a) (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    (hdiff : ∀ t ∈ Ioo a b,
      0 ≤ deriv (fun s ↦ (F.connection s).scalarCurvature (γ t)) t +
        mvfderiv (𝓡 n) (F.connection t).scalarCurvature (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) +
        (F.connection t).scalarCurvature (γ t) / (t - T) +
        (F.metric t).inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) / 2 *
          (F.connection t).scalarCurvature (γ t)) :
    (F.connection a).scalarCurvature (γ a) * (a - T) *
        Real.exp (-PoincareMT.spacetimeEnergy F γ a b / 2) ≤
      (F.connection b).scalarCurvature (γ b) * (b - T) := by
  let H : FiniteHarnackPath T a b := {
    hTa := hTa
    hab := hab.le
    f := fun t ↦ (F.connection t).scalarCurvature (γ t)
    f' := fun t ↦ deriv (fun s ↦ (F.connection s).scalarCurvature (γ t)) t +
      mvfderiv (𝓡 n) (F.connection t).scalarCurvature (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
    speedSq := fun t ↦ (F.metric t).inner (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
    f_continuous := scalarCurvature_continuousOn_path hM04 J F γ hJ hγ.continuousOn
    speed_continuous := continuousOn_spacetimeEnergy_integrand F hab hJ γ hγ
    speed_integrable := intervalIntegrable_spacetimeEnergy_integrand F hab hJ γ hγ
    derivative := fun _ ht ↦ scalarCurvature_hasDerivAt_path hM04 F hJ γ hγ ht
    differential := hdiff }
  exact H.integrated

theorem ancient_integrated_of_path_differential
    (hM04 : PoincareMT.RicciFlowCurvatureCalculus.{u})
    (F : PoincareMT.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    (hdiff : ∀ t ∈ Ioo a b,
      0 ≤ deriv (fun s ↦ (F.connection s).scalarCurvature (γ t)) t +
        mvfderiv (𝓡 n) (F.connection t).scalarCurvature (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) +
        (F.metric t).inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) / 2 *
          (F.connection t).scalarCurvature (γ t)) :
    (F.connection a).scalarCurvature (γ a) *
        Real.exp (-PoincareMT.spacetimeEnergy F γ a b / 2) ≤
      (F.connection b).scalarCurvature (γ b) := by
  let H : AncientHarnackPath a b := {
    hab := hab.le
    f := fun t ↦ (F.connection t).scalarCurvature (γ t)
    f' := fun t ↦ deriv (fun s ↦ (F.connection s).scalarCurvature (γ t)) t +
      mvfderiv (𝓡 n) (F.connection t).scalarCurvature (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
    speedSq := fun t ↦ (F.metric t).inner (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1)
    f_continuous := scalarCurvature_continuousOn_path hM04 J F γ hJ hγ.continuousOn
    speed_continuous := continuousOn_spacetimeEnergy_integrand F hab hJ γ hγ
    speed_integrable := intervalIntegrable_spacetimeEnergy_integrand F hab hJ γ hγ
    derivative := fun _ ht ↦ scalarCurvature_hasDerivAt_path hM04 F hJ γ hγ ht
    differential := hdiff }
  exact H.integrated

theorem integrated_at_terminal_of_finite_origins_flow_of_contMDiff
    (hM04 : PoincareMT.RicciFlowCurvatureTheory.{u})
    (F : PoincareMT.RicciFlow n M J) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    {x₁ x₂ : M} (hγa : γ a = x₁) (hγb : γ b = x₂)
    (finite : ∀ t ∈ Ioo a b, ∀ᶠ T : ℝ in atBot,
      (F.connection a).scalarCurvature x₁ * (a - T) *
          Real.exp (-PoincareMT.spacetimeEnergy F γ a t / 2) ≤
        (F.connection t).scalarCurvature (γ t) * (t - T)) :
    (F.connection a).scalarCurvature x₁ *
        Real.exp (-PoincareMT.spacetimeEnergy F γ a b / 2) ≤
      (F.connection b).scalarCurvature x₂ := by
  exact Poincare.RicciFlow.Harnack.integrated_at_terminal_of_finite_origins_flow
    F hab γ hγa hγb
    (scalarCurvature_continuousOn_path hM04 J F γ hJ hγ.continuousOn)
    (intervalIntegrable_spacetimeEnergy_integrand F hab hJ γ hγ) finite

private theorem path_differential_of_half_velocity [T2Space M]
    {g : PoincareMT.RiemannianMetric n M} (D : PoincareMT.LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hcurv : D.NonnegativeCurvatureOperator x)
    (v : TangentSpace (𝓡 n) x) (dR c : ℝ)
    (hdiff : 0 ≤ dR + c +
      2 * mvfderiv (𝓡 n) D.scalarCurvature x ((1 / 2 : ℝ) • v) +
      2 * D.ricci x ((1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v)) :
    0 ≤ dR + mvfderiv (𝓡 n) D.scalarCurvature x v + c +
      g.inner x v v / 2 * D.scalarCurvature x := by
  have hbound := (D.ricci_bounds_of_nonnegative_curvatureOperator
    hD x hcurv ((1 / 2 : ℝ) • v)).2
  simp only [map_smul, smul_apply, smul_eq_mul] at hdiff hbound
  nlinarith

/-- The finite differential estimate gives the frozen zero-safe path estimate. -/
theorem finite_integrated_of_differential [T2Space M]
    (hM04 : PoincareMT.RicciFlowCurvatureTheory.{u})
    {T₀ T₁ a b : ℝ} (hTa : T₀ < a) (hab : a < b) (hbT : b < T₁)
    (F : PoincareMT.RicciFlow n M (Ioo T₀ T₁))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hdiff : ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n) (F.connection t).scalarCurvature x v +
          2 * (F.connection t).ricci x v v)
    (γ : ℝ → M) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    {x₁ x₂ : M} (hγa : γ a = x₁) (hγb : γ b = x₂) :
    (F.connection a).scalarCurvature x₁ * (a - T₀) *
        Real.exp (-PoincareMT.spacetimeEnergy F γ a b / 2) ≤
      (F.connection b).scalarCurvature x₂ * (b - T₀) := by
  rw [← hγa, ← hγb]
  have hJ : Icc a b ⊆ Ioo T₀ T₁ :=
    fun _ ht ↦ ⟨hTa.trans_le ht.1, ht.2.trans_lt hbT⟩
  apply finite_integrated_of_path_differential hM04 F hTa hab hJ γ hγ
  intro t ht
  have htJ := hJ ⟨ht.1.le, ht.2.le⟩
  let v := mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1
  obtain ⟨dR, hdR, hi⟩ := hdiff t htJ (γ t) ((1 / 2 : ℝ) • v)
  rw [(hdR.hasDerivAt (Ioo_mem_nhds htJ.1 htJ.2)).deriv]
  exact path_differential_of_half_velocity (F.connection t)
    (hM04.tensor_calculus n M (F.metric t) (F.connection t))
    (γ t) (hcurv t htJ (γ t)) v dR _ hi

/-- The ancient differential estimate gives the path estimate up to time zero. -/
theorem ancient_integrated_of_differential [T2Space M]
    (hM04 : PoincareMT.RicciFlowCurvatureCalculus.{u})
    (F : PoincareMT.RicciFlow n M (Iic 0))
    (hcurv : ∀ t ≤ 0, ∀ x : M, (F.connection t).NonnegativeCurvatureOperator x)
    (hdiff : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR (Iic 0) t ∧
        0 ≤ dR + 2 * mvfderiv (𝓡 n) (F.connection t).scalarCurvature x v +
          2 * (F.connection t).ricci x v v)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0)
    (γ : ℝ → M) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Icc a b))
    {x₁ x₂ : M} (hγa : γ a = x₁) (hγb : γ b = x₂) :
    (F.connection a).scalarCurvature x₁ *
        Real.exp (-PoincareMT.spacetimeEnergy F γ a b / 2) ≤
      (F.connection b).scalarCurvature x₂ := by
  rw [← hγa, ← hγb]
  have hJ : Icc a b ⊆ Iic (0 : ℝ) := fun _ ht ↦ ht.2.trans hb
  apply ancient_integrated_of_path_differential hM04 F hab hJ γ hγ
  intro t ht
  have ht0 : t < 0 := ht.2.trans_le hb
  let v := mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1
  obtain ⟨dR, hdR, hi⟩ := hdiff t ht0.le (γ t) ((1 / 2 : ℝ) • v)
  rw [(hdR.hasDerivAt (Iic_mem_nhds ht0)).deriv]
  simpa only [add_zero] using path_differential_of_half_velocity (F.connection t)
    (hM04.tensor_calculus n M (F.metric t) (F.connection t))
    (γ t) (hcurv t ht0.le (γ t)) v dR 0 (by simpa only [add_zero] using hi)

/-! Assemble the finite path estimate with the exact ancient field assignment.
The finite producer remains the only geometric input; all path and endpoint
consumers are supplied here. -/
theorem with_path_harnack (hM04 : PoincareMT.RicciFlowCurvatureTheory.{u})
    (H : PoincareMT.HarnackAncientTheory.{u}) :
    PoincareMT.HarnackAncientTheory.{u} := by
  let H' := Poincare.Geometry.RicciFlow.Harnack.with_ancient_harnack hM04 H
  refine { H' with
    finite_integrated := ?_, ancient_integrated := ?_ }
  · intro n M _ _ _ _ _ _ T₀ T₁ t₁ t₂ hT₀ h₁₂ h₂T₁ F hcomplete hcurv hbound
      γ hγ x₁ x₂ hγ₁ hγ₂
    refine finite_integrated_of_differential hM04 hT₀ h₁₂ h₂T₁ F
      (fun t ht x ↦ hcurv t ht x) ?_ γ hγ hγ₁ hγ₂
    intro t ht x v
    obtain ⟨dR, hdR, hineq⟩ := H.finite_differential n M T₀ T₁
      (lt_trans (lt_trans hT₀ h₁₂) h₂T₁) F hcomplete hcurv hbound t ht x v
    exact ⟨dR, hdR, hineq⟩
  · intro n M _ _ _ _ _ _ _ F hcomplete hcurv hbound hnonflat
    intro t₁ t₂ ht₁₂ ht₂ γ hγ x₁ x₂ hγ₁ hγ₂
    refine ancient_integrated_of_differential hM04 F
      (fun t ht x ↦ hcurv t ht x) ?_ ht₁₂ ht₂ γ hγ hγ₁ hγ₂
    intro t ht x v
    exact H'.ancient_differential n M F hcomplete hcurv hbound hnonflat t ht x v

/-! The finite differential producer is the sole geometric input needed to
assemble the frozen M06 structure.  This constructor is kept separate from
the producer so its exact field assignment can be checked before that result
is published. -/
theorem assemble_harnack_from_finite_differential
    (hM04 : PoincareMT.RicciFlowCurvatureTheory.{u})
    (hfinite :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [T3Space M] [SecondCountableTopology M],
        ∀ T₀ T₁ : ℝ, T₀ < T₁ →
        ∀ F : PoincareMT.RicciFlow n M (Set.Ioo T₀ T₁),
        (∀ t ∈ Set.Ioo T₀ T₁, PoincareMT.MetricComplete (F.metric t)) →
        (∀ t ∈ Set.Ioo T₀ T₁, ∀ x : M,
          PoincareMT.LeviCivitaData.NonnegativeCurvatureOperator
            (F.connection t) x) →
        (∀ t ∈ Set.Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
          ∀ x : M, PoincareMT.LeviCivitaData.CurvatureOperatorBound
            (F.connection t) K x) →
        ∀ t ∈ Set.Ioo T₀ T₁, ∀ x : M,
          ∀ v : TangentSpace (𝓡 n) x, ∃ dR : ℝ,
            HasDerivWithinAt
                (fun s ↦ (F.connection s).scalarCurvature x) dR
                (Set.Ioo T₀ T₁) t ∧
            0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
              2 * mvfderiv (𝓡 n)
                (fun y ↦ (F.connection t).scalarCurvature y) x v +
              2 * (F.connection t).ricci x v v) :
    PoincareMT.HarnackAncientTheory.{u} := by
  refine
    { metric_edist_transport := fun n M _ _ _ _ g x y ↦
        Poincare.Geometry.RicciFlow.Harnack.metric_edist_transport g x y
      finite_differential := hfinite
      finite_integrated := ?_
      ancient_differential := ?_
      ancient_integrated := ?_ }
  · intro n M _ _ _ _ _ _ T₀ T₁ t₁ t₂ hT₀ h₁₂ h₂T₁ F hcomplete hcurv hbound
      γ hγ x₁ x₂ hγ₁ hγ₂
    refine finite_integrated_of_differential hM04 hT₀ h₁₂ h₂T₁ F
      (fun t ht x ↦ hcurv t ht x) ?_ γ hγ hγ₁ hγ₂
    intro t ht x v
    obtain ⟨dR, hdR, hineq⟩ := hfinite n M T₀ T₁
      (lt_trans (lt_trans hT₀ h₁₂) h₂T₁) F hcomplete hcurv hbound t ht x v
    exact ⟨dR, hdR, hineq⟩
  · intro n M _ _ _ _ _ _ _ F hcomplete hcurv hbound _
    intro t ht x v
    exact Poincare.Geometry.RicciFlow.Harnack.ancient_differential_of_finite
      hM04 hfinite F hcomplete hcurv hbound t ht x v
  · intro n M _ _ _ _ _ _ _ F hcomplete hcurv hbound _
    intro t₁ t₂ ht₁₂ ht₂ γ hγ x₁ x₂ hγ₁ hγ₂
    refine ancient_integrated_of_differential hM04 F
      (fun t ht x ↦ hcurv t ht x) ?_ ht₁₂ ht₂ γ hγ hγ₁ hγ₂
    intro t ht x v
    exact Poincare.Geometry.RicciFlow.Harnack.ancient_differential_of_finite
      hM04 hfinite F hcomplete hcurv hbound t ht x v

end Poincare.Geometry.RicciFlow.Harnack
