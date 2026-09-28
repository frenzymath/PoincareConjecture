import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Piece

open Set Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareConjecture.ConjugateVariation

open PoincareConjecture.ConnectionVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_deriv_intervalIntegral_of_contDiffOn_box
    {F : ℝ → ℝ → ℝ} {a b s₀ r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F)
            (Set.Ioo (s₀ - r) (s₀ + r) ×ˢ Set.Ioo (a - r) (b + r))) :
    HasDerivAt (deriv (fun σ => ∫ t in a..b, F σ t))
      (∫ t in a..b, deriv (fun σ => deriv (fun ρ => F ρ t) σ) s₀) s₀ := by
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
  exact (hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hG1 hs₀).congr_of_eventuallyEq hEq

section Piece

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℝ × ℝ → E}

theorem hasDerivAt_pieceEnergy {τ₀ τ₁ r : ℝ} {U : Set E}
    (hτ : τ₀ ≤ τ₁) (hr : 0 < r)
    (hG : ContDiffOn ℝ 2 G U) (hu : ContDiff ℝ 3 u)
    (humem : ∀ p ∈ Set.Ioo (-r) r ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r), u p ∈ U)
    {s : ℝ} (hs : s ∈ Set.Ioo (-r) r) :
    HasDerivAt (fun σ => ∫ t in τ₀..τ₁, energyDensity G u (0, 1) (σ, t))
      (∫ t in τ₀..τ₁, deriv (fun ρ => energyDensity G u (0, 1) (ρ, t)) s) s := by
  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ)))
      (Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r)) := by
    refine contDiffOn_energyDensity hG hu (fun p hp => humem p ⟨?_, hp.2⟩) _
    have := hp.1
    simpa using this
  have hf1 : ContDiffOn ℝ 1 (energyDensity G u ((0 : ℝ), (1 : ℝ)))
      (Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r)) :=
    hf2.of_le (by norm_num)
  have hs' : s ∈ Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) := by simpa using hs
  exact hasDerivAt_intervalIntegral_of_contDiffOn_box
    (F := fun σ t => energyDensity G u ((0 : ℝ), (1 : ℝ)) (σ, t)) hτ hr hf1 hs'

theorem hasDerivAt_deriv_pieceEnergy_chartIndexIntegrand {τ₀ τ₁ r : ℝ} {U : Set E}
    (hτ : τ₀ ≤ τ₁) (hr : 0 < r) (hU : IsOpen U)
    (hGsymm : ∀ x X Y, G x X Y = G x Y X)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hcompat : ∀ x ∈ U, IsMetricCompatibleAt G Γ x)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U)
    (hu : ContDiff ℝ 3 u)
    (humem : ∀ p ∈ Set.Ioo (-r) r ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r), u p ∈ U)
    (hgeo : ∀ t ∈ Set.Icc τ₀ τ₁,
      covDerivAlong Γ u (fun q => fderiv ℝ u q (0, 1)) (0, 1) (0, t) = 0)
    (hj₀ : covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (1, 0) (0, τ₀) = 0)
    (hj₁ : covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (1, 0) (0, τ₁) = 0) :
    HasDerivAt (deriv (fun s => ∫ t in τ₀..τ₁, energyDensity G u (0, 1) (s, t)))
      (∫ t in τ₀..τ₁, chartIndexIntegrand G Γ u t) 0 := by

  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ)))
      (Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r)) := by
    refine contDiffOn_energyDensity hG hu (fun p hp => humem p ⟨?_, hp.2⟩) _
    have := hp.1
    simpa using this

  have hHD := hasDerivAt_deriv_intervalIntegral_of_contDiffOn_box
    (F := fun σ t => energyDensity G u ((0 : ℝ), (1 : ℝ)) (σ, t)) hτ hr hf2

  have hval := deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand hτ hr hU hGsymm hΓsymm
    hcompat hG hΓ hu humem hgeo hj₀ hj₁
  rw [hHD.deriv] at hval
  rw [← hval]
  exact hHD

end Piece

section Sum

variable {N : ℕ} {f f' : ℕ → ℝ → ℝ} {L : ℕ → ℝ} {ε : ℝ}

private theorem funext_sum_range (g : ℕ → ℝ → ℝ) (n : ℕ) :
    (fun s : ℝ => ∑ i ∈ Finset.range n, g i s) = ∑ i ∈ Finset.range n, g i := by
  funext s
  simp

theorem hasDerivAt_deriv_sum (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s)
    (hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0) :
    HasDerivAt (deriv (fun s => ∑ i ∈ Finset.range N, f i s))
      (∑ i ∈ Finset.range N, L i) 0 := by
  have hnhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε
  have hEq : deriv (fun s => ∑ i ∈ Finset.range N, f i s)
      =ᶠ[𝓝 (0 : ℝ)] fun s => ∑ i ∈ Finset.range N, f' i s := by
    filter_upwards [hnhds] with s hs
    rw [funext_sum_range f N]
    exact (HasDerivAt.sum (fun i hi => hd i (Finset.mem_range.mp hi) s hs)).deriv
  have hsum2 : HasDerivAt (fun s => ∑ i ∈ Finset.range N, f' i s)
      (∑ i ∈ Finset.range N, L i) 0 := by
    rw [funext_sum_range f' N]
    exact HasDerivAt.sum (fun i hi => hd2 i (Finset.mem_range.mp hi))
  exact hsum2.congr_of_eventuallyEq hEq

theorem deriv_deriv_sum_eq (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s)
    (hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0) :
    deriv (deriv (fun s => ∑ i ∈ Finset.range N, f i s)) 0 = ∑ i ∈ Finset.range N, L i :=
  (hasDerivAt_deriv_sum hε hd hd2).deriv

theorem continuousAt_sum (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s) :
    ContinuousAt (fun s => ∑ i ∈ Finset.range N, f i s) 0 := by
  rw [funext_sum_range f N]
  exact (HasDerivAt.sum
    (fun i hi => hd i (Finset.mem_range.mp hi) 0 ⟨by linarith, hε⟩)).continuousAt

theorem sum_nonneg_of_isLocalMin (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s)
    (hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0)
    (hmin : IsLocalMin (fun s => ∑ i ∈ Finset.range N, f i s) 0) :
    0 ≤ ∑ i ∈ Finset.range N, L i := by
  rw [← deriv_deriv_sum_eq hε hd hd2]
  exact deriv_deriv_nonneg_of_isLocalMin hmin (continuousAt_sum hε hd)

end Sum

end PoincareConjecture.ConjugateVariation

end
