import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSecondJetContinuity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ActualRawInterior










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure X)

private theorem component_cutoff_source (K : Set X)
    (A : Fin n → Fin n → 𝓢(X, ℝ)) (hA : ∀ i j x, A i j x = A j i x)
    (u : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (B Z : PiLp 2 (fun _ : Fin n => dirichletValue K))
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) Z =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) B - principalVectorEnergy K A z u)
    (χ : 𝓢(X, ℝ)) (hχK : tsupport χ ⊆ K) (k : Fin n) (φ : 𝓢(X, ℝ)) :
    principalEnergy K A (u k) (intoDirichletForm K (cutoffSupportedTest K χ hχK φ)) =
      inner ℝ (schwartzMultiplier χ ((B k : L2) - (Z k : L2))) (φ.toLp 2 volume) := by
  have h := vector_component_divergence K A hA u B Z heq k (cutoffSupportedTest K χ hχK φ)
  change principalEnergy K A (u k) (intoDirichletForm K (cutoffSupportedTest K χ hχK φ)) =
    inner ℝ ((B k : L2) - (Z k : L2)) ((schwartzProduct χ φ).toLp 2 volume) at h
  rw [schwartzProduct_toLp, ← schwartzMultiplier_selfAdjoint] at h
  exact h

theorem raw_heat_coherent_secondJets_continuous {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (W : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hW : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ W t)
    (heq : ∀ t ∈ Ioo a b, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (deriv W t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection t) hK.isClosed η hη (W t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη)
                z (W t))
    (χ : 𝓢(X, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (k : Fin n) :
    ∃ q : Ioo a b → List (Fin n) → L2,
      (∀ t, q t [] = localizedDirichletValue K χ (W t k)) ∧
      (∀ t i, q t [i] = localizedDirichletPartial K χ (W t k) i) ∧
      (∀ t s, IsWeakSchwartzJet (q t) s) ∧
      ∀ v, v.length ≤ 2 → Continuous (fun t : Ioo a b => q t v) := by
  have hj (t : Ioo a b) (s : ℕ) : HasInteriorWeakJets K (W t k) s := by
    simpa only [iteratedDeriv_zero] using
      (raw_compact_heat_all_spatial_jets F hab hJ hK η hη hηK W hW heq t.property s 0 k).mono
        (Nat.le_succ s)
  choose q hq0 hq1 hq using fun t : Ioo a b =>
    exists_coherent_interior_jet (W t k) (hj t) χ hχ hχK
  let I := finiteHilbertMap (m := n) (dirichletInclusion K)
  let L := fun t => rawLowerFormOperator (F.connection t) hK.isClosed η hη
  let G : ℝ → L2 := fun t => schwartzMultiplier χ
    ((L t (W t) k : L2) - (I (deriv W t) k : L2))
  have huk (t : ℝ) (ht : t ∈ Ioo a b) : ContDiffAt ℝ ∞ (fun s => W s k) t :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => dirichletForm K) k).contDiff.contDiffAt.comp t
      (hW t ht)
  have hG : ContinuousOn G (Ioo a b) := by
    intro t ht
    have hLc : ContDiffAt ℝ ∞ L t :=
      (contDiffOn_rawLowerFormOperator F hab hJ hK.isClosed η hη).contDiffAt
        (Icc_mem_nhds ht.1 ht.2)
    have hdW : ContDiffAt ℝ ∞ (deriv W) t := by
      simpa only [iteratedDeriv_one] using contDiffAt_iteratedDeriv_infty (hW t ht) 1
    let ev : PiLp 2 (fun _ : Fin n => dirichletValue K) →L[ℝ] L2 :=
      (dirichletValue K).subtypeL.comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => dirichletValue K) k)
    exact ((schwartzMultiplier χ).continuous.continuousAt.comp
      ((ev.continuous.continuousAt.comp ((hLc.clm_apply (hW t ht)).continuousAt)).sub
        (ev.continuous.continuousAt.comp
          (I.continuous.continuousAt.comp hdW.continuousAt)))).continuousWithinAt
  have htest (t : ℝ) (ht : t ∈ Ioo a b) (φ : 𝓢(X, ℝ)) :
      principalEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη)
        (W t k) (intoDirichletForm K
          (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
            inner ℝ (G t) (φ.toLp 2 volume) :=
    component_cutoff_source K _
      (rawCutoffPrincipalCoefficient_symmetric (F.metric t) η hη) (W t)
      (L t (W t)) (I (deriv W t)) (heq t ht) χ (hχK.trans interior_subset) k φ
  have hsecond := raw_localized_secondJet_continuous F hab hJ Ioo_subset_Icc_self hK η hη hηK
    χ hχ hχK (fun t => W t k) G
    (fun t ht => (huk t ht).continuousAt.continuousWithinAt) hG htest
    q hq0 hq1 (fun t => hq t 2)
  refine ⟨q, hq0, hq1, hq, ?_⟩
  intro v hv
  have hu : Continuous (fun t : Ioo a b => W t k) :=
    continuous_iff_continuousAt.mpr (fun t => (huk t t.property).continuousAt.comp
      continuous_subtype_val.continuousAt)
  cases v with
  | nil =>
    simpa only [hq0, localizedDirichletValue, Function.comp_def,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
      (schwartzMultiplier χ).continuous.comp
        (((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.comp hu)
  | cons i v =>
    cases v with
    | nil =>
      simpa only [hq1, localizedDirichletPartial, Function.comp_def, Pi.add_def,
        ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
        ((schwartzMultiplier χ).continuous.comp ((dirichletPartial K i).continuous.comp hu)).add
          ((schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)).continuous.comp
            (((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.comp hu))
    | cons j v =>
      have hv0 : v = [] := by
        have hvlen : v.length = 0 := by simp only [List.length_cons] at hv; omega
        exact List.length_eq_zero_iff.mp hvlen
      subst v
      exact hsecond j i

end PoincareConjecture.M35.Uniqueness.Heat
