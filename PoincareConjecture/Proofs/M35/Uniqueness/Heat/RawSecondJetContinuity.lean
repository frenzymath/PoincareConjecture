import PoincareConjecture.Proofs.M35.Uniqueness.Heat.EllipticJetContinuity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LocalizedSourceSmooth
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialCoefficientBound
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.RawUniformRestart
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffWeakEquation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter Metric
open scoped SchwartzMap LineDeriv ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure X)

private theorem multiplier_sub (a b : 𝓢(X, ℝ)) :
    schwartzMultiplier (a - b) = schwartzMultiplier a - schwartzMultiplier b :=
  schwartzMultiplierLinear.map_sub a b

private theorem derivative_multiplier_sub (a b : 𝓢(X, ℝ)) (v : X) :
    schwartzMultiplier (∂_{v} (a - b)) =
      schwartzMultiplier (∂_{v} a) - schwartzMultiplier (∂_{v} b) := by
  have he : ∂_{v} (a - b) = ∂_{v} a - ∂_{v} b :=
    (LineDeriv.lineDerivOpCLM ℝ 𝓢(X, ℝ) v).map_sub a b
  rw [he, multiplier_sub]

theorem raw_localized_secondJet_continuous {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {I : Set ℝ} (hI : I ⊆ Icc a b)
    {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (χ : 𝓢(X, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : ℝ → dirichletForm K) (G : ℝ → L2)
    (hu : ContinuousOn u I) (hG : ContinuousOn G I)
    (heq : ∀ t ∈ I, ∀ φ : 𝓢(X, ℝ),
      principalEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη)
        (u t) (intoDirichletForm K
          (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
            inner ℝ (G t) (φ.toLp 2 volume))
    (q : I → List (Fin n) → L2)
    (hq0 : ∀ t, q t [] = localizedDirichletValue K χ (u t))
    (hq1 : ∀ t i, q t [i] = localizedDirichletPartial K χ (u t) i)
    (hq : ∀ t, IsWeakSchwartzJet (q t) 2) (i j : Fin n) :
    Continuous (fun t : I => q t [j, i]) := by
  let A := fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη
  let source := fun t => G t + localizedDivergenceSource K (A t) χ (u t) 0
  have hAc (r s : Fin n) : Continuous (fun v : I => schwartzMultiplier (A v r s)) :=
    ((contDiffOn_raw_principalMultiplier F hab hJ η hη r s).continuousOn.mono
      hI).domRestrict
  have hdAc (r s : Fin n) : Continuous (fun v : I => schwartzMultiplier
      (∂_{EuclideanSpace.single s (1 : ℝ)} (A v r s))) :=
    ((contDiffOn_rawPrincipal_spatial_multiplier F hab hJ η hη r s s).continuousOn.mono
      hI).domRestrict
  have hsource : Continuous (fun t : I => source t) :=
    hG.domRestrict.add
      (continuous_localizedDivergenceSource K (fun t : I => A t) χ
        (fun t : I => u t) (fun _ => 0) hAc hdAc hu.domRestrict continuous_const)
  obtain ⟨δ, hδ, hδK⟩ := hχ.exists_cthickening_subset_open isOpen_interior hχK
  let r := δ / 3
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hthick : cthickening (3 * r) (tsupport χ) ⊆ K := by
    rw [show 3 * r = δ by dsimp only [r]; ring]
    exact hδK.trans interior_subset
  obtain ⟨ell, hell, hEll⟩ := ValueInitial.exists_raw_slab_cutoff_ellipticity
    F isCompact_Icc hJ hK η hη hηK
  obtain ⟨D, hD, hAD⟩ := exists_rawPrincipal_slab_derivative_bound
    F isCompact_Icc hJ η hη
  have hsupport (t : I) : ∀ᵐ x ∂volume, x ∉ tsupport χ → q t [] x = 0 := by
    rw [hq0 t]
    exact localizedDirichletValue_ae_support K χ (u t)
  have hdiv (t : I) : DivergenceEquation (A t) (fun k => q t [k]) (source t)
      (cthickening (3 * r) (tsupport χ)) := by
    intro φ _ _
    simp only [hq1]
    exact localized_divergence_of_cutoff_tests K (A t) χ (hχK.trans interior_subset)
      (u t) (G t) (heq t t.property) φ
  apply continuous_iff_continuousAt.mpr
  intro t
  have huc : ContinuousAt (fun s : I => u s) t := hu.domRestrict.continuousAt
  have hfirst (k : Fin n) : Tendsto (fun s : I => q s [k]) (𝓝 t) (𝓝 (q t [k])) := by
    have hv :=
      ((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.continuousAt.comp huc
    have hp := (dirichletPartial K k).continuous.continuousAt.comp huc
    simpa only [hq1, localizedDirichletPartial, Function.comp_def, Pi.add_def,
      ContinuousLinearMap.comp_apply] using!
      (((schwartzMultiplier χ).continuous.continuousAt.comp hp).add
        ((schwartzMultiplier (∂_{EuclideanSpace.single k (1 : ℝ)} χ)).continuous.continuousAt.comp
          hv)).tendsto
  have hmul (k l : Fin n) : Tendsto (fun s : I =>
      schwartzMultiplier (A s k l - A t k l)) (𝓝 t) (𝓝 0) := by
    have hc := (hAc k l).continuousAt (x := t)
    simpa only [multiplier_sub, sub_self] using hc.tendsto.sub_const
      (schwartzMultiplier (A t k l))
  have hdmul (k l : Fin n) : Tendsto (fun s : I =>
      schwartzMultiplier (∂_{EuclideanSpace.single l (1 : ℝ)} (A s k l - A t k l)))
      (𝓝 t) (𝓝 0) := by
    have hc := (hdAc k l).continuousAt (x := t)
    simpa only [derivative_multiplier_sub, sub_self] using hc.tendsto.sub_const
      (schwartzMultiplier (∂_{EuclideanSpace.single l (1 : ℝ)} (A t k l)))
  exact tendsto_weak_secondJet_of_divergence (fun s : I => A s) (A t) q (q t)
    (fun s => source s) (source t) hq (hq t) hχ hsupport (hsupport t) hr hell hD
    (fun s x hx => hEll s (hI s.property) x (hthick hx))
    (fun s => hAD s (hI s.property)) hdiv (hdiv t) hsource.continuousAt.tendsto
    hfirst hmul hdmul i j

end PoincareConjecture.M35.Uniqueness.Heat
