import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod












noncomputable section

namespace PoincareConjecture.ConjugateVariation


open scoped Topology
open Set Filter MeasureTheory


theorem deriv_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x₀ : ℝ}
    (hmin : IsLocalMin f x₀) (hc : ContinuousAt f x₀) :
    0 ≤ deriv (deriv f) x₀ := by
  by_contra hcon
  have hneg : deriv (deriv f) x₀ < 0 := not_le.mp hcon
  have hd : deriv f x₀ = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x₀ := isLocalMax_of_deriv_deriv_neg hneg hd hc
  have hEq : f =ᶠ[𝓝 x₀] fun _ => f x₀ := by
    filter_upwards [hmin, hmax] with x h1 h2 using le_antisymm h2 h1
  have h1 : deriv f =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
    have := hEq.deriv
    filter_upwards [this] with x hx
    simpa using hx
  have : deriv (deriv f) x₀ = deriv (fun _ => (0 : ℝ)) x₀ := h1.deriv_eq
  rw [this, deriv_const] at hneg
  exact lt_irrefl _ hneg

section Box

variable {F : ℝ → ℝ → ℝ} {a b s₀ r : ℝ}



theorem continuousOn_slice {g : ℝ × ℝ → ℝ} {I J : Set ℝ} (hg : ContinuousOn g (I ×ˢ J))
    {σ : ℝ} (hσ : σ ∈ I) : ContinuousOn (fun t => g (σ, t)) J :=
  hg.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht => ⟨hσ, ht⟩


theorem hasDerivAt_partial_of_contDiffOn_box
    (hF : ContDiffOn ℝ 1 (Function.uncurry F)
            (Set.Ioo (s₀ - r) (s₀ + r) ×ˢ Set.Ioo (a - r) (b + r)))
    {σ t : ℝ} (hσ : σ ∈ Set.Ioo (s₀ - r) (s₀ + r)) (ht : t ∈ Set.Ioo (a - r) (b + r)) :
    HasDerivAt (fun ρ => F ρ t)
      (fderiv ℝ (Function.uncurry F) (σ, t) ((1 : ℝ), (0 : ℝ))) σ := by
  have hU : IsOpen (Set.Ioo (s₀ - r) (s₀ + r) ×ˢ Set.Ioo (a - r) (b + r)) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hmem : ((σ, t) : ℝ × ℝ) ∈ Set.Ioo (s₀ - r) (s₀ + r) ×ˢ Set.Ioo (a - r) (b + r) :=
    ⟨hσ, ht⟩
  have hdiff : DifferentiableAt ℝ (Function.uncurry F) (σ, t) :=
    ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hmem))
  have hfd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (σ, t)) (σ, t) :=
    hdiff.hasFDerivAt
  have hg : HasDerivAt (fun ρ : ℝ => (ρ, t)) ((1 : ℝ), (0 : ℝ)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ t)
  exact hfd.comp_hasDerivAt σ hg


theorem hasDerivAt_intervalIntegral_of_contDiffOn_box
    {F : ℝ → ℝ → ℝ} {a b s₀ r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiffOn ℝ 1 (Function.uncurry F)
            (Set.Ioo (s₀ - r) (s₀ + r) ×ˢ Set.Ioo (a - r) (b + r)))
    {s : ℝ} (hs : s ∈ Set.Ioo (s₀ - r) (s₀ + r)) :
    HasDerivAt (fun σ => ∫ t in a..b, F σ t)
      (∫ t in a..b, deriv (fun σ => F σ t) s) s := by
  set I : Set ℝ := Set.Ioo (s₀ - r) (s₀ + r) with hI
  set J : Set ℝ := Set.Ioo (a - r) (b + r) with hJ
  have hIccJ : Set.Icc a b ⊆ J := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

  set F' : ℝ → ℝ → ℝ := fun σ t => fderiv ℝ (Function.uncurry F) (σ, t) ((1 : ℝ), (0 : ℝ))
    with hF'def
  have hHD : ∀ σ ∈ I, ∀ t ∈ J, HasDerivAt (fun ρ => F ρ t) (F' σ t) σ := by
    intro σ hσ t ht
    exact hasDerivAt_partial_of_contDiffOn_box hF hσ ht

  have hUopen : IsOpen (I ×ˢ J) := isOpen_Ioo.prod isOpen_Ioo
  have hFcont : ContinuousOn (Function.uncurry F) (I ×ˢ J) := hF.continuousOn
  have hfdcont : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p) (I ×ˢ J) :=
    hF.continuousOn_fderiv_of_isOpen hUopen le_rfl
  have hF'cont : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (I ×ˢ J) := by
    exact ContinuousOn.clm_apply hfdcont continuousOn_const

  set ρ : ℝ := min (s - (s₀ - r)) ((s₀ + r) - s) / 2 with hρdef
  have hρpos : 0 < ρ := by
    have h1 : 0 < s - (s₀ - r) := by linarith [hs.1]
    have h2 : 0 < (s₀ + r) - s := by linarith [hs.2]
    have hmpos : 0 < min (s - (s₀ - r)) ((s₀ + r) - s) := lt_min h1 h2
    rw [hρdef]; linarith
  have hIccI : Set.Icc (s - ρ) (s + ρ) ⊆ I := by
    intro x hx
    have h1 : 0 < s - (s₀ - r) := by linarith [hs.1]
    have h2 : 0 < (s₀ + r) - s := by linarith [hs.2]
    have hm1 : ρ < s - (s₀ - r) := by
      have : min (s - (s₀ - r)) ((s₀ + r) - s) ≤ s - (s₀ - r) := min_le_left _ _
      have hmpos : 0 < min (s - (s₀ - r)) ((s₀ + r) - s) := lt_min h1 h2
      rw [hρdef]; linarith
    have hm2 : ρ < (s₀ + r) - s := by
      have : min (s - (s₀ - r)) ((s₀ + r) - s) ≤ (s₀ + r) - s := min_le_right _ _
      have hmpos : 0 < min (s - (s₀ - r)) ((s₀ + r) - s) := lt_min h1 h2
      rw [hρdef]; linarith
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hK : IsCompact (Set.Icc (s - ρ) (s + ρ) ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  have hKU : Set.Icc (s - ρ) (s + ρ) ×ˢ Set.Icc a b ⊆ I ×ˢ J :=
    Set.prod_mono hIccI hIccJ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'cont.mono hKU)

  set S : Set ℝ := Set.Ioo (s - ρ) (s + ρ) with hS
  have hSnhds : S ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hSI : S ⊆ I := fun x hx => hIccI (Set.Ioo_subset_Icc_self hx)
  have huIoc : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  have hIocIcc : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self

  have hslice : ∀ σ ∈ I, ContinuousOn (fun t => F σ t) (Set.Icc a b) := by
    intro σ hσ
    exact (continuousOn_slice hFcont hσ).mono hIccJ
  have hslice' : ∀ σ ∈ I, ContinuousOn (fun t => F' σ t) (Set.Icc a b) := by
    intro σ hσ
    exact (continuousOn_slice (g := fun p : ℝ × ℝ => F' p.1 p.2) hF'cont hσ).mono hIccJ
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (x₀ := s) (bound := fun _ => C) (s := S) hSnhds
    (Filter.eventually_of_mem (mem_of_superset hSnhds (fun x hx => hSI hx) : I ∈ 𝓝 s)
      (fun x hx => by
        rw [huIoc]
        exact ((hslice x hx).mono hIocIcc).aestronglyMeasurable measurableSet_Ioc))
    (((hslice s hs).mono (Set.uIcc_of_le hab).subset).intervalIntegrable)
    (by rw [huIoc]; exact ((hslice' s hs).mono hIocIcc).aestronglyMeasurable measurableSet_Ioc)
    (Filter.Eventually.of_forall (fun t ht x hx => by
      rw [huIoc] at ht
      exact hC (x, t) ⟨Set.Ioo_subset_Icc_self hx, hIocIcc ht⟩))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t ht x hx => by
      rw [huIoc] at ht
      exact hHD x (hSI hx) t (hIccJ (hIocIcc ht))))
  have hcongr : ∀ t ∈ Set.uIcc a b, deriv (fun σ => F σ t) s = F' s t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (hHD s hs t (hIccJ ht)).deriv
  rw [intervalIntegral.integral_congr hcongr]
  exact key.2


theorem deriv_deriv_intervalIntegral_of_contDiffOn_box
    {F : ℝ → ℝ → ℝ} {a b s₀ r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F)
            (Set.Ioo (s₀ - r) (s₀ + r) ×ˢ Set.Ioo (a - r) (b + r))) :
    deriv (deriv (fun σ => ∫ t in a..b, F σ t)) s₀
      = ∫ t in a..b, deriv (fun σ => deriv (fun ρ => F ρ t) σ) s₀ := by
  set I : Set ℝ := Set.Ioo (s₀ - r) (s₀ + r) with hI
  set J : Set ℝ := Set.Ioo (a - r) (b + r) with hJ
  have hUopen : IsOpen (I ×ˢ J) := isOpen_Ioo.prod isOpen_Ioo
  have hs₀ : s₀ ∈ I := ⟨by linarith, by linarith⟩
  have hInhds : I ∈ 𝓝 s₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hF1 : ContDiffOn ℝ 1 (Function.uncurry F) (I ×ˢ J) := hF.of_le (by norm_num)

  set G : ℝ → ℝ → ℝ := fun σ t => deriv (fun ρ => F ρ t) σ with hGdef
  have hG1 : ContDiffOn ℝ 1 (Function.uncurry G) (I ×ˢ J) := by
    have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p) (I ×ˢ J) :=
      ContDiffOn.fderiv_of_isOpen hF hUopen (by norm_num)
    have happ : ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p ((1 : ℝ), (0 : ℝ))) (I ×ˢ J) :=
      ContDiffOn.clm_apply hfd contDiffOn_const
    refine happ.congr ?_
    rintro ⟨σ, t⟩ ⟨hσ, ht⟩
    exact (hasDerivAt_partial_of_contDiffOn_box hF1 hσ ht).deriv

  have hEq : deriv (fun σ => ∫ t in a..b, F σ t) =ᶠ[𝓝 s₀] fun σ => ∫ t in a..b, G σ t := by
    filter_upwards [hInhds] with σ hσ
    exact (hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hF1 hσ).deriv
  rw [hEq.deriv_eq]
  exact (hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hG1 hs₀).deriv

end Box

end PoincareConjecture.ConjugateVariation

end
