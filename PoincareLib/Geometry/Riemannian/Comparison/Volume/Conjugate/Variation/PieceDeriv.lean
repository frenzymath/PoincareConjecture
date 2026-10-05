import PoincareLib.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Piece

/-!
# Differentiable second variation and finite sums

Derivative forms of the interval-energy identities, including the finite-sum
rules used for broken variations. Adapted from AxelWorkspace,
`formalized-sources/riemannian/MorganTian/MorganTianLib/Foundations/PieceEnergyDeriv.lean`,
revision `f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e` (Apache-2.0).
Original SHA-256: 9dca67fee84ee064d9bc7b0589cd7897f15297f1ca0db8d578a9b97d8cfe575c.
License: `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`.
Imports and namespaces are adapted to the current variation modules.
Supports Morgan--Tian, Theorem 1.34, p. 19.
-/

open Set Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareMT.ConjugateVariation

open PoincareMT.ConnectionVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The second-level `HasDerivAt` for a parametric interval integral -/

/-- **Math.** `HasDerivAt` form of the second derivative of an interval integral in a
parameter: for `F` of class `C²` on an open box, the function `σ ↦ deriv (σ ↦ ∫ F σ t) σ` is
itself differentiable at the centre `s₀`, with derivative `∫ ∂²_s F`.

This is the differentiable upgrade of
`EnergyVariation.deriv_deriv_intervalIntegral_of_contDiffOn_box`, whose proof already produces
the eventual equality `deriv (∫ F) =ᶠ[𝓝 s₀] ∫ ∂_s F` on a neighbourhood of `s₀`; we finish with
`HasDerivAt.congr_of_eventuallyEq` rather than reading off the value. -/
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
  -- the partial `s`-derivative family
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
  -- the first derivative, valid on a whole neighbourhood of `s₀`
  have hEq : deriv (fun σ => ∫ t in a..b, F σ t) =ᶠ[𝓝 s₀] fun σ => ∫ t in a..b, G σ t := by
    filter_upwards [hInhds] with σ hσ
    exact (hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hF1 hσ).deriv
  exact (hasDerivAt_intervalIntegral_of_contDiffOn_box hab hr hG1 hs₀).congr_of_eventuallyEq hEq

/-! ### The two derivatives of one piece energy -/

section Piece

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℝ × ℝ → E}

/-- **Math.** The **first** `s`-derivative of the energy of one piece, at *every* `s` in the
neighbourhood `Ioo (-r) r` of `0`:

`d/ds ∫_{τ₀}^{τ₁} e(s, t) dt = ∫_{τ₀}^{τ₁} ∂_s e(s, t) dt`.

Differentiation under the integral sign; the only input is that the energy density is `C¹`
(indeed `C²`) on the open box, which follows from `contDiffOn_energyDensity`.

This is needed — beyond the value of the second derivative at `0` — because `deriv` of a
finite sum only splits where every summand is differentiable, and for the *second* derivative
of the sum that has to hold on a whole neighbourhood of `0`. -/
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

/-- **Math.** **`HasDerivAt` form of the second variation of one piece.**

Under the hypotheses of `deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand` (the `t`-lines
are geodesic on `[τ₀, τ₁]` at `s = 0`, and the two junction curves `s ↦ u(s, τⱼ)` are geodesics
at `s = 0`, so that the piece kills its own boundary term), the *first* derivative of the piece
energy is itself differentiable at `0`, with

`d/ds (d/ds E_piece) (0) = ∫_{τ₀}^{τ₁} (G(∇_t Y, ∇_t Y) − G(R(Y,X)X, Y)) dt`.

*Proof.*  No analysis is redone.  `hasDerivAt_deriv_intervalIntegral_of_contDiffOn_box` at
`s₀ = 0` already gives `HasDerivAt (deriv E_piece) L 0` for `L = ∫ ∂²_s e`; hence
`deriv (deriv E_piece) 0 = L`.  The existing
`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand` says the same left-hand side equals
`∫ chartIndexIntegrand`, so `L = ∫ chartIndexIntegrand` and the value in the `HasDerivAt` can
be rewritten. ∎ -/
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
  -- the energy density is `C²` on the open box: exactly the step used inside
  -- `deriv_deriv_pieceEnergy_eq_boundary_add_integral`
  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ)))
      (Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r)) := by
    refine contDiffOn_energyDensity hG hu (fun p hp => humem p ⟨?_, hp.2⟩) _
    have := hp.1
    simpa using this
  -- the abstract `HasDerivAt` at the second level, with the *analytic* value
  have hHD := hasDerivAt_deriv_intervalIntegral_of_contDiffOn_box
    (F := fun σ t => energyDensity G u ((0 : ℝ), (1 : ℝ)) (σ, t)) hτ hr hf2
  -- the *geometric* value, from the existing piece computation
  have hval := deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand hτ hr hU hGsymm hΓsymm
    hcompat hG hΓ hu humem hgeo hj₀ hj₁
  rw [hHD.deriv] at hval
  rw [← hval]
  exact hHD

end Piece

/-! ### The finite-sum rules

Abstract: no energies, no charts.  These are what turn the per-piece statements above into a
statement about the total energy `𝓔 (s) = ∑ i ∈ Finset.range N, Eᵢ s` of a broken variation. -/

section Sum

variable {N : ℕ} {f f' : ℕ → ℝ → ℝ} {L : ℕ → ℝ} {ε : ℝ}

/-- The pointwise finite sum of a family of functions is the `Finset.sum` of the family in the
function space.  (`HasDerivAt.sum` is stated for the latter; the caller's total energy is
written as the former.) -/
private theorem funext_sum_range (g : ℕ → ℝ → ℝ) (n : ℕ) :
    (fun s : ℝ => ∑ i ∈ Finset.range n, g i s) = ∑ i ∈ Finset.range n, g i := by
  funext s
  simp

/-- **Math.** The finite sum of functions that are differentiable on a neighbourhood of `0`,
whose derivatives are themselves differentiable at `0`, has a twice-differentiable sum:

`deriv (∑ᵢ fᵢ)` has derivative `∑ᵢ Lᵢ` at `0`.

*Proof.*  On `Ioo (-ε) ε`, `HasDerivAt.sum` gives `HasDerivAt (∑ᵢ fᵢ) (∑ᵢ f'ᵢ s) s`, hence
`deriv (∑ᵢ fᵢ) =ᶠ[𝓝 0] ∑ᵢ f'ᵢ` — the `Ioo` is a neighbourhood of `0`, which is exactly why the
first derivatives are needed on a whole neighbourhood and not merely at `0`.  A second
`HasDerivAt.sum` differentiates `∑ᵢ f'ᵢ` at `0`, and `congr_of_eventuallyEq` transports it back
to `deriv (∑ᵢ fᵢ)`. ∎ -/
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

/-- **Math.** Value form of `hasDerivAt_deriv_sum`: the second derivative of a finite sum at `0`
is the sum of the second derivatives. -/
theorem deriv_deriv_sum_eq (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s)
    (hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0) :
    deriv (deriv (fun s => ∑ i ∈ Finset.range N, f i s)) 0 = ∑ i ∈ Finset.range N, L i :=
  (hasDerivAt_deriv_sum hε hd hd2).deriv

/-- **Math.** A finite sum of functions differentiable near `0` is continuous at `0`.

Needed to feed `deriv_deriv_nonneg_of_isLocalMin`, whose second-derivative test at a local
minimum requires continuity of the function at the point. -/
theorem continuousAt_sum (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s) :
    ContinuousAt (fun s => ∑ i ∈ Finset.range N, f i s) 0 := by
  rw [funext_sum_range f N]
  exact (HasDerivAt.sum
    (fun i hi => hd i (Finset.mem_range.mp hi) 0 ⟨by linarith, hε⟩)).continuousAt

/-- The second variations of finitely many pieces have nonnegative sum when
their total energy has a local minimum. -/
theorem sum_nonneg_of_isLocalMin (hε : 0 < ε)
    (hd : ∀ i < N, ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s)
    (hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0)
    (hmin : IsLocalMin (fun s => ∑ i ∈ Finset.range N, f i s) 0) :
    0 ≤ ∑ i ∈ Finset.range N, L i := by
  rw [← deriv_deriv_sum_eq hε hd hd2]
  exact deriv_deriv_nonneg_of_isLocalMin hmin (continuousAt_sum hε hd)

end Sum

end PoincareMT.ConjugateVariation

end
