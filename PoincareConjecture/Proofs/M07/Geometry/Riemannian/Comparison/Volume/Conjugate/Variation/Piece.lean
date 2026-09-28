import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Density
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Energy
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus














open Set Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareConjecture.ConjugateVariation

open PoincareConjecture.ConnectionVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]









theorem hasDerivAt_slice_fst {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun σ => f (σ, t)) (fderiv ℝ f (s, t) ((1 : ℝ), (0 : ℝ))) s :=
  hf.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))


theorem deriv_slice_fst {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    deriv (fun σ => f (σ, t)) s = fderiv ℝ f (s, t) ((1 : ℝ), (0 : ℝ)) :=
  (hasDerivAt_slice_fst hf).deriv



theorem hasDerivAt_slice_snd {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun τ => f (s, τ)) (fderiv ℝ f (s, t) ((0 : ℝ), (1 : ℝ))) t :=
  hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))


theorem deriv_slice_snd {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    deriv (fun τ => f (s, τ)) t = fderiv ℝ f (s, t) ((0 : ℝ), (1 : ℝ)) :=
  (hasDerivAt_slice_snd hf).deriv

















section Regularity

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]




theorem contDiffOn_covDerivAlong {Γ : E → E →L[ℝ] E →L[ℝ] E} {u V : P → E}
    {U : Set E} {s : Set P} (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 2 u)
    (hV : ContDiff ℝ 2 V) (hmaps : Set.MapsTo u s U) (d : P) :
    ContDiffOn ℝ 1 (covDerivAlong Γ u V d) s := by
  have h1 : ContDiff ℝ 1 (fun q : P => fderiv ℝ V q d) :=
    (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h2 : ContDiffOn ℝ 1 (fun q : P => Γ (u q)) s :=
    hΓ.comp (hu.of_le (by norm_num)).contDiffOn hmaps
  have h3 : ContDiff ℝ 1 (fun q : P => fderiv ℝ u q d) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h4 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have h : covDerivAlong Γ u V d
      = fun q : P => fderiv ℝ V q d + Γ (u q) (fderiv ℝ u q d) (V q) := rfl
  rw [h]
  exact h1.contDiffOn.add ((h2.clm_apply h3.contDiffOn).clm_apply h4.contDiffOn)



theorem contDiffOn_energyDensity {G : E → E →L[ℝ] E →L[ℝ] ℝ} {u : P → E}
    {U : Set E} {s : Set P} (hG : ContDiffOn ℝ 2 G U) (hu : ContDiff ℝ 3 u)
    (hmaps : Set.MapsTo u s U) (dt : P) :
    ContDiffOn ℝ 2 (energyDensity G u dt) s := by
  have hX : ContDiff ℝ 2 (fun q : P => fderiv ℝ u q dt) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hGu : ContDiffOn ℝ 2 (fun q : P => G (u q)) s :=
    hG.comp (hu.of_le (by norm_num)).contDiffOn hmaps
  have h : energyDensity G u dt
      = fun q : P => (1 / 2 : ℝ) * G (u q) (fderiv ℝ u q dt) (fderiv ℝ u q dt) := rfl
  rw [h]
  exact contDiffOn_const.mul ((hGu.clm_apply hX.contDiffOn).clm_apply hX.contDiffOn)

end Regularity





def chartIndexIntegrand (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℝ × ℝ → E) (t : ℝ) : ℝ :=
  G (u (0, t))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (0, 1) (0, t))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (0, 1) (0, t))
    - G (u (0, t))
        (christoffelCurvature Γ (u (0, t)) (fderiv ℝ u (0, t) (1, 0))
          (fderiv ℝ u (0, t) (0, 1)) (fderiv ℝ u (0, t) (0, 1)))
        (fderiv ℝ u (0, t) (1, 0))


def secondVariationBoundary (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℝ × ℝ → E) (t : ℝ) : ℝ :=
  G (u (0, t))
    (covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (1, 0) (0, t))
    (fderiv ℝ u (0, t) (0, 1))

section Piece

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℝ × ℝ → E}



private def boundaryFun (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℝ × ℝ → E) : ℝ × ℝ → ℝ :=
  fun q => G (u q) (covDerivAlong Γ u (fun r => fderiv ℝ u r ((1 : ℝ), (0 : ℝ)))
    ((1 : ℝ), (0 : ℝ)) q) (fderiv ℝ u q ((0 : ℝ), (1 : ℝ)))

private theorem contDiffOn_boundaryFun {U : Set E} {s : Set (ℝ × ℝ)}
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hmaps : Set.MapsTo u s U) : ContDiffOn ℝ 1 (boundaryFun G Γ u) s := by
  have hY2 : ContDiff ℝ 2 (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hcov : ContDiffOn ℝ 1 (covDerivAlong Γ u
      (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ))) s :=
    contDiffOn_covDerivAlong hΓ (hu.of_le (by norm_num)) hY2 hmaps _
  have hX1 : ContDiff ℝ 1 (fun q : ℝ × ℝ => fderiv ℝ u q ((0 : ℝ), (1 : ℝ))) :=
    ((hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  have hGu : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => G (u q)) s :=
    (hG.of_le (by norm_num)).comp (hu.of_le (by norm_num)).contDiffOn hmaps
  exact (hGu.clm_apply hcov).clm_apply hX1.contDiffOn



theorem contDiffOn_secondVariationBoundary {U : Set E} {J : Set ℝ}
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hJ : ∀ t ∈ J, u ((0 : ℝ), t) ∈ U) :
    ContDiffOn ℝ 1 (secondVariationBoundary G Γ u) J := by
  have hb : ContDiffOn ℝ 1 (boundaryFun G Γ u) (u ⁻¹' U) :=
    contDiffOn_boundaryFun hG hΓ hu (fun q hq => hq)
  have hline : ContDiff ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) := contDiff_const.prodMk contDiff_id
  exact hb.comp hline.contDiffOn (fun t ht => hJ t ht)



theorem continuousOn_chartIndexIntegrand {U : Set E} {J : Set ℝ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hJ : ∀ t ∈ J, u ((0 : ℝ), t) ∈ U) :
    ContinuousOn (chartIndexIntegrand G Γ u) J := by
  have hline : Continuous (fun t : ℝ => ((0 : ℝ), t)) := continuous_const.prodMk continuous_id
  have hmapsW : Set.MapsTo u (u ⁻¹' U) U := fun q hq => hq
  have hmapsJ : Set.MapsTo (fun t : ℝ => ((0 : ℝ), t)) J (u ⁻¹' U) := fun t ht => hJ t ht
  have hY2 : ContDiff ℝ 2 (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hT2 : ContDiff ℝ 2 (fun r : ℝ × ℝ => fderiv ℝ u r ((0 : ℝ), (1 : ℝ))) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hx : ContinuousOn (fun t : ℝ => u ((0 : ℝ), t)) J := (hu.continuous.comp hline).continuousOn
  have hxmaps : Set.MapsTo (fun t : ℝ => u ((0 : ℝ), t)) J U := fun t ht => hJ t ht
  have hX : ContinuousOn (fun t : ℝ => fderiv ℝ u ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ))) J :=
    (hY2.continuous.comp hline).continuousOn
  have hT : ContinuousOn (fun t : ℝ => fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ))) J :=
    (hT2.continuous.comp hline).continuousOn
  have hD : ContinuousOn (fun t : ℝ => covDerivAlong Γ u
      (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), t)) J :=
    (contDiffOn_covDerivAlong hΓ (hu.of_le (by norm_num)) hY2 hmapsW _).continuousOn.comp
      hline.continuousOn hmapsJ
  have hΓc : ContinuousOn (fun t : ℝ => Γ (u ((0 : ℝ), t))) J := hΓ.continuousOn.comp hx hxmaps
  have hdΓ : ContinuousOn (fun t : ℝ => fderiv ℝ Γ (u ((0 : ℝ), t))) J :=
    (hΓ.continuousOn_fderiv_of_isOpen hU le_rfl).comp hx hxmaps
  have hGc : ContinuousOn (fun t : ℝ => G (u ((0 : ℝ), t))) J := hG.continuousOn.comp hx hxmaps
  have hR : ContinuousOn (fun t : ℝ => christoffelCurvature Γ (u ((0 : ℝ), t))
      (fderiv ℝ u ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)))) J :=
    ((((hdΓ.clm_apply hX).clm_apply hT).clm_apply hT).sub
        (((hdΓ.clm_apply hT).clm_apply hX).clm_apply hT)
      |>.add ((hΓc.clm_apply hX).clm_apply ((hΓc.clm_apply hT).clm_apply hT)))
      |>.sub ((hΓc.clm_apply hT).clm_apply ((hΓc.clm_apply hX).clm_apply hT))
  exact ((hGc.clm_apply hD).clm_apply hD).sub ((hGc.clm_apply hR).clm_apply hX)






theorem deriv_deriv_slice_energyDensity {t : ℝ} {U : Set E} (hU : IsOpen U)
    (hGsymm : ∀ x X Y, G x X Y = G x Y X)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hcompat : ∀ x ∈ U, IsMetricCompatibleAt G Γ x)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hmem : u ((0 : ℝ), t) ∈ U)
    (hgeo : covDerivAlong Γ u (fun q => fderiv ℝ u q (0, 1)) (0, 1) (0, t) = 0) :
    deriv (fun σ : ℝ => deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ) 0
      = deriv (secondVariationBoundary G Γ u) t + chartIndexIntegrand G Γ u t := by

  have hWopen : IsOpen (u ⁻¹' U) := hU.preimage hu.continuous
  have hmapsW : Set.MapsTo u (u ⁻¹' U) U := fun q hq => hq
  have hW0 : ((0 : ℝ), t) ∈ u ⁻¹' U := hmem
  have hWnhds : u ⁻¹' U ∈ 𝓝 ((0 : ℝ), t) := hWopen.mem_nhds hW0
  have hUnhds : U ∈ 𝓝 (u ((0 : ℝ), t)) := hU.mem_nhds hmem
  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ))) (u ⁻¹' U) :=
    contDiffOn_energyDensity hG hu hmapsW _

  have hsliceOpen : IsOpen {σ : ℝ | (σ, t) ∈ u ⁻¹' U} :=
    hWopen.preimage (continuous_id.prodMk continuous_const)
  have hinner :
      (fun σ : ℝ => deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ)
        =ᶠ[𝓝 (0 : ℝ)] fun σ : ℝ =>
          fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) (σ, t) ((1 : ℝ), (0 : ℝ)) := by
    filter_upwards [hsliceOpen.mem_nhds (show (0 : ℝ) ∈ {σ : ℝ | (σ, t) ∈ u ⁻¹' U} from hW0)]
      with σ hσ
    exact deriv_slice_fst
      ((hf2.contDiffAt (hWopen.mem_nhds hσ)).differentiableAt (by norm_num))

  have hg1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ =>
      fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) q ((1 : ℝ), (0 : ℝ))) (u ⁻¹' U) :=
    (hf2.fderiv_of_isOpen hWopen (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have houter : HasDerivAt
      (fun σ : ℝ => fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) (σ, t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fun q : ℝ × ℝ =>
          fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) q ((1 : ℝ), (0 : ℝ)))
        ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ))) 0 :=
    hasDerivAt_slice_fst (f := fun q : ℝ × ℝ =>
      fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) q ((1 : ℝ), (0 : ℝ)))
      ((hg1.contDiffAt hWnhds).differentiableAt (by norm_num))
  rw [hinner.deriv_eq, houter.deriv]

  have hsv := secondVariation_energyDensity (G := G) (Γ := Γ) (u := u) (p := ((0 : ℝ), t))
    (ds := ((1 : ℝ), (0 : ℝ))) (dt := ((0 : ℝ), (1 : ℝ)))
    hGsymm (by filter_upwards [hUnhds] with x hx using hcompat x hx) hΓsymm
    (hG.contDiffAt hUnhds) hu.contDiffAt
    ((hΓ.contDiffAt hUnhds).differentiableAt (by norm_num)) hgeo
  rw [hsv]

  have hbdry : deriv (secondVariationBoundary G Γ u) t
      = fderiv ℝ (fun q : ℝ × ℝ => G (u q)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r ((1 : ℝ), (0 : ℝ)))
            ((1 : ℝ), (0 : ℝ)) q) (fderiv ℝ u q ((0 : ℝ), (1 : ℝ))))
          ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)) :=
    (hasDerivAt_slice_snd (f := boundaryFun G Γ u)
      (((contDiffOn_boundaryFun hG hΓ hu hmapsW).contDiffAt hWnhds).differentiableAt (by norm_num))).deriv
  rw [hbdry, chartIndexIntegrand]
  ring














theorem deriv_deriv_pieceEnergy_eq_boundary_add_integral {τ₀ τ₁ r : ℝ} {U : Set E}
    (hτ : τ₀ ≤ τ₁) (hr : 0 < r) (hU : IsOpen U)
    (hGsymm : ∀ x X Y, G x X Y = G x Y X)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hcompat : ∀ x ∈ U, IsMetricCompatibleAt G Γ x)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U)
    (hu : ContDiff ℝ 3 u)
    (humem : ∀ p ∈ Set.Ioo (-r) r ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r), u p ∈ U)
    (hgeo : ∀ t ∈ Set.Icc τ₀ τ₁,
      covDerivAlong Γ u (fun q => fderiv ℝ u q (0, 1)) (0, 1) (0, t) = 0) :
    deriv (deriv (fun s => ∫ t in τ₀..τ₁, energyDensity G u (0, 1) (s, t))) 0
      = (secondVariationBoundary G Γ u τ₁ - secondVariationBoundary G Γ u τ₀)
        + ∫ t in τ₀..τ₁, chartIndexIntegrand G Γ u t := by

  set J : Set ℝ := Set.Ioo (τ₀ - r) (τ₁ + r) with hJdef
  have hJmem : ∀ t ∈ J, u ((0 : ℝ), t) ∈ U := fun t ht =>
    humem ((0 : ℝ), t) ⟨⟨by linarith, by linarith⟩, ht⟩
  have hsub : Set.uIcc τ₀ τ₁ ⊆ J := by
    rw [Set.uIcc_of_le hτ]
    exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩

  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ)))
      (Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r)) := by
    refine contDiffOn_energyDensity hG hu (fun p hp => humem p ⟨?_, hp.2⟩) _
    have := hp.1
    simpa using this
  have hbox : deriv (deriv
        (fun s : ℝ => ∫ t in τ₀..τ₁, energyDensity G u ((0 : ℝ), (1 : ℝ)) (s, t))) 0
      = ∫ t in τ₀..τ₁, deriv
          (fun σ : ℝ => deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ) 0 :=
    deriv_deriv_intervalIntegral_of_contDiffOn_box hτ hr hf2
  rw [hbox]

  have hpt : ∀ t ∈ Set.uIcc τ₀ τ₁,
      deriv (fun σ : ℝ =>
          deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ) 0
        = deriv (secondVariationBoundary G Γ u) t + chartIndexIntegrand G Γ u t := by
    intro t ht
    have htJ : t ∈ J := hsub ht
    rw [Set.uIcc_of_le hτ] at ht
    exact deriv_deriv_slice_energyDensity hU hGsymm hΓsymm hcompat hG hΓ hu (hJmem t htJ)
      (hgeo t ht)
  rw [intervalIntegral.integral_congr hpt]

  have hΦ1 : ContDiffOn ℝ 1 (secondVariationBoundary G Γ u) J :=
    contDiffOn_secondVariationBoundary hG hΓ hu hJmem
  have hcΦ : ContinuousOn (deriv (secondVariationBoundary G Γ u)) J :=
    hΦ1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcI : ContinuousOn (chartIndexIntegrand G Γ u) J :=
    continuousOn_chartIndexIntegrand hU hG hΓ hu hJmem
  rw [intervalIntegral.integral_add ((hcΦ.mono hsub).intervalIntegrable)
    ((hcI.mono hsub).intervalIntegrable)]



  have hftc : (∫ t in τ₀..τ₁, deriv (secondVariationBoundary G Γ u) t)
      = secondVariationBoundary G Γ u τ₁ - secondVariationBoundary G Γ u τ₀ :=
    intervalIntegral.integral_deriv_eq_sub' _ rfl
      (fun x hx =>
        (hΦ1.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt (by norm_num))
      (hcΦ.mono hsub)
  rw [hftc]













theorem deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand {τ₀ τ₁ r : ℝ} {U : Set E}
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
    deriv (deriv (fun s => ∫ t in τ₀..τ₁, energyDensity G u (0, 1) (s, t))) 0
      = ∫ t in τ₀..τ₁, chartIndexIntegrand G Γ u t := by
  have h₀ : secondVariationBoundary G Γ u τ₀ = 0 := by
    show G (u ((0 : ℝ), τ₀))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ)))
        ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), τ₀)) (fderiv ℝ u ((0 : ℝ), τ₀) ((0 : ℝ), (1 : ℝ))) = 0
    rw [hj₀]
    simp
  have h₁ : secondVariationBoundary G Γ u τ₁ = 0 := by
    show G (u ((0 : ℝ), τ₁))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ)))
        ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), τ₁)) (fderiv ℝ u ((0 : ℝ), τ₁) ((0 : ℝ), (1 : ℝ))) = 0
    rw [hj₁]
    simp
  rw [deriv_deriv_pieceEnergy_eq_boundary_add_integral hτ hr hU hGsymm hΓsymm hcompat hG hΓ hu
    humem hgeo, h₀, h₁]
  ring

end Piece

end PoincareConjecture.ConjugateVariation

end
