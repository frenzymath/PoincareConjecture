import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Action
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.BackwardPath
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variational ReducedLengthMinimum.Variation.Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem regularizedLIntegrand_contDiffOn_of_smooth (K : AncientKappaSolution 2 M)
    (α : ℝ → M) {U : Set ℝ} (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α U) :
    ContDiffOn ℝ ∞ (regularizedLIntegrand K.flow 0 α) U := by
  have hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 2)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin 2)) (α s)
        (curveVelocity (n := 2) α s)) U :=
    contMDiffOn_mfderiv_const_apply hU α hα 1
  have ht : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ ↦ 0 - s ^ 2) U :=
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
  have hmem : MapsTo (fun s : ℝ ↦ 0 - s ^ 2) U (Iic 0) := by
    intro s _
    exact sub_nonpos.mpr (sq_nonneg s)
  have hg := (movingMetric_pair_contMDiffOn K.flow (fun s : ℝ ↦ 0 - s ^ 2) α
    (curveVelocity (n := 2) α) (curveVelocity (n := 2) α) ht hα hA hA hmem).contDiffOn
  have hV := (K.regularizedPotential_contMDiff.comp_contMDiffOn
    (contMDiffOn_id.prodMk hα)).contDiffOn
  exact hV.add (contDiffOn_const.mul hg)

theorem regularizedLIntegrand_intervalIntegrable_of_smooth (K : AncientKappaSolution 2 M)
    (α : ℝ → M) {U : Set ℝ} (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α U)
    {τ : ℝ} (hI : Icc 0 (Real.sqrt τ) ⊆ U) :
    IntervalIntegrable (regularizedLIntegrand K.flow 0 α) volume 0 (Real.sqrt τ) := by
  have hcont : ContinuousOn (regularizedLIntegrand K.flow 0 α) (Icc 0 (Real.sqrt τ)) :=
    (K.regularizedLIntegrand_contDiffOn_of_smooth α hU hα).continuousOn.mono hI
  exact hcont.intervalIntegrable_of_Icc (Real.sqrt_nonneg τ)

theorem exists_lVariation_of_smoothSquareFamily (K : AncientKappaSolution 2 M)
    {τ : ℝ} (p : BackwardTimePath K.flow 0 0 τ)
    (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 2) ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hI : Icc 0 (Real.sqrt τ) ×ˢ Ioo (-ρ) ρ ⊆ U)
    (hcenter : ∀ s ∈ Icc 0 (Real.sqrt τ), f (s, 0) = p.curve (s ^ 2)) :
    ∃ V : LVariation K.flow 0 0 τ p,
      V.radius = ρ ∧ (∀ s u, V.squareFamily s u = f (s, u)) ∧
      (∀ u, EqOn (fun t ↦ V.family t u) (fun t ↦ f (Real.sqrt t, u)) (Icc 0 τ)) ∧
      ∀ u, variationLLength V u =
        backwardLLength K.flow 0 0 τ (fun t ↦ f (Real.sqrt t, u)) := by
  classical
  let family : ℝ → ℝ → M := fun t u ↦ if u = 0 then p.curve t else f (Real.sqrt t, u)
  have heq (u : ℝ) : EqOn (fun t ↦ family t u)
      (fun t ↦ f (Real.sqrt t, u)) (Icc 0 τ) := by
    intro t ht
    by_cases hu : u = 0
    · subst u
      simp only [family, if_pos rfl]
      have hs : Real.sqrt t ∈ Icc 0 (Real.sqrt τ) :=
        ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩
      simpa only [Real.sq_sqrt ht.1] using (hcenter (Real.sqrt t) hs).symm
    · simp only [family, if_neg hu]
  let V : LVariation K.flow 0 0 τ p := {
    family := family
    at_zero := fun t ↦ by simp only [family, if_pos rfl]
    radius := ρ
    radius_pos := hρ
    squareFamily := fun s u ↦ f (s, u)
    squareDomain := U
    square_open := hU
    square_contains := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hI
    square_smooth := hf
    square_agrees := by
      intro s hs u _
      have hs0 : 0 ≤ s := by
        simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
      have hsτ : s ^ 2 ≤ τ := by
        have h := mul_self_le_mul_self hs0 hs.2
        simpa only [← pow_two, Real.sq_sqrt p.ordered.le] using h
      have h := heq u (show s ^ 2 ∈ Icc 0 τ from ⟨sq_nonneg s, hsτ⟩)
      simpa only [Real.sqrt_sq hs0] using h.symm
    l_integrable := by
      intro u hu
      by_cases hu0 : u = 0
      · subst u
        simpa only [family, if_pos rfl] using p.l_integrable
      · let D := (fun s : ℝ ↦ (s, u)) ⁻¹' U
        have hD : IsOpen D := hU.preimage (continuous_id.prodMk continuous_const)
        have hDI : Icc 0 (Real.sqrt τ) ⊆ D := fun s hs ↦ hI ⟨hs, hu⟩
        have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun s ↦ f (s, u)) D :=
          hf.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
        have hcont : ContinuousOn (fun s ↦ f (s, u)) (Icc (Real.sqrt 0) (Real.sqrt τ)) := by
          simpa only [Real.sqrt_zero] using hα.continuousOn.mono hDI
        have hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 (fun s ↦ f (s, u))
            (Ioo (Real.sqrt 0) (Real.sqrt τ)) := by
          simpa only [Real.sqrt_zero] using
            (hα.of_le (by simp)).mono (Ioo_subset_Icc_self.trans hDI)
        have hint : IntervalIntegrable (regularizedLIntegrand K.flow 0 (fun s ↦ f (s, u)))
            volume (Real.sqrt 0) (Real.sqrt τ) := by
          simpa only [Real.sqrt_zero] using
            K.regularizedLIntegrand_intervalIntegrable_of_smooth (fun s ↦ f (s, u)) hD hα hDI
        let Q := backwardPathOfSqrt K.flow 0 0 τ p.nonnegative p.ordered p.terminal_mem
          p.time_mem (fun s ↦ f (s, u)) hcont hreg hint
        simpa only [Q, backwardPathOfSqrt, family, if_neg hu0] using Q.l_integrable
  }
  refine ⟨V, rfl, fun _ _ ↦ rfl, heq, ?_⟩
  intro u
  change backwardLLength K.flow 0 0 τ (fun t ↦ family t u) = _
  unfold backwardLLength
  apply intervalIntegral.integral_congr_Ioo_of_le p.ordered.le
  intro t ht
  have hnear : (fun r ↦ family r u) =ᶠ[𝓝 t] (fun r ↦ f (Real.sqrt r, u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact heq u (Ioo_subset_Icc_self hr)
  have hd := hnear.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2)
  have hvalue : family t u = f (Real.sqrt t, u) := heq u (Ioo_subset_Icc_self ht)
  simp only [backwardLIntegrand, curveVelocity, hd]
  rw [hvalue]

theorem exists_initialFixedLVariation_of_smoothSquareFamily (K : AncientKappaSolution 2 M)
    {τ : ℝ} (p : BackwardTimePath K.flow 0 0 τ)
    (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 2) ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hI : Icc 0 (Real.sqrt τ) ×ˢ Ioo (-ρ) ρ ⊆ U)
    (hcenter : ∀ s ∈ Icc 0 (Real.sqrt τ), f (s, 0) = p.curve (s ^ 2))
    (hleft : ∀ u ∈ Ioo (-ρ) ρ, f (0, u) = f (0, 0)) :
    ∃ V : InitialFixedLVariation K.flow 0 0 τ p,
      V.radius = ρ ∧ (∀ s u, V.squareFamily s u = f (s, u)) ∧
      (∀ u, EqOn (fun t ↦ V.family t u) (fun t ↦ f (Real.sqrt t, u)) (Icc 0 τ)) ∧
      ∀ u, variationLLength V.toLVariation u =
        backwardLLength K.flow 0 0 τ (fun t ↦ f (Real.sqrt t, u)) := by
  obtain ⟨V, hVr, hVf, hVeq, hVa⟩ :=
    K.exists_lVariation_of_smoothSquareFamily p f U hU hf ρ hρ hI hcenter
  have hfix : ∀ u ∈ Ioo (-V.radius) V.radius, V.family 0 u = p.curve 0 := by
    intro u hu
    have hu' : u ∈ Ioo (-ρ) ρ := by simpa only [hVr] using hu
    have h1 := hVeq u (show (0 : ℝ) ∈ Icc 0 τ from ⟨le_rfl, p.ordered.le⟩)
    have h0 := hVeq 0 (show (0 : ℝ) ∈ Icc 0 τ from ⟨le_rfl, p.ordered.le⟩)
    dsimp only at h1 h0
    rw [Real.sqrt_zero, hleft u hu'] at h1
    rw [Real.sqrt_zero, V.at_zero] at h0
    exact h1.trans h0.symm
  exact ⟨{ toLVariation := V, fixed_left := hfix }, hVr, hVf, hVeq, hVa⟩

end PoincareConjecture.AncientKappaSolution
