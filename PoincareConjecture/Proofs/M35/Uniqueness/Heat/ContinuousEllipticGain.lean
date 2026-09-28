import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousLocalizedSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CommutatorContinuity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CommutedJetContinuity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.CutoffWeakEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter Metric
open scoped SchwartzMap LineDeriv Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

private theorem multiplier_sub (a b : 𝓢(V, ℝ)) :
    schwartzMultiplier (a - b) = schwartzMultiplier a - schwartzMultiplier b :=
  schwartzMultiplierLinear.map_sub a b

private theorem derivative_multiplier_sub (a b : 𝓢(V, ℝ)) (i : Fin n) :
    schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} (a - b)) =
      schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} a) -
        schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} b) := by
  have he : ∂_{EuclideanSpace.single i (1 : ℝ)} (a - b) =
      ∂_{EuclideanSpace.single i (1 : ℝ)} a - ∂_{EuclideanSpace.single i (1 : ℝ)} b :=
    (LineDeriv.lineDerivOpCLM ℝ 𝓢(V, ℝ) (EuclideanSpace.single i (1 : ℝ))).map_sub a b
  rw [he, multiplier_sub]

theorem hasContinuousWeakJet_of_cutoff_tests
    (K : Set V) (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) {s : ℕ}
    (hA : ∀ i j w, w.length ≤ s + 1 →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t i j))))
    (χ : 𝓢(V, ℝ)) (hχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ interior K)
    (u : ι → dirichletForm K) (hu : HasContinuousInteriorJets K u (s + 1))
    (G : ι → L2) (hG : HasContinuousWeakJet G s)
    (heq : ∀ t (φ : 𝓢(V, ℝ)), principalEnergy K (A t) (u t)
      (intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
        inner ℝ (G t) (φ.toLp 2 volume))
    {r ell D : ℝ} (hr : 0 < r) (hell : 0 < ell) (hD : 0 ≤ D)
    (hEll : ∀ t, ∀ x ∈ cthickening (3 * r) (tsupport χ), ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A t i j x * ξ i * ξ j)
    (hAD : ∀ t i j x, ‖fderiv ℝ (A t i j) x‖ ≤ D) :
    HasContinuousWeakJet (fun t => localizedDirichletValue K χ (u t)) (s + 2) := by
  have hex (t : ι) : HasFiniteWeakJet (localizedDirichletValue K χ (u t)) (s + 2) :=
    exists_localized_jet_of_cutoff_tests K (A t) χ hχ hχK (u t) (hu.slice t)
      (G t) (hG.slice t) (heq t) hr hell hD (hEll t) (hAD t)
  choose q hq0 hq using hex
  obtain ⟨p, hp0, hp, hpc⟩ := hu χ hχ hχK
  have hlow (w : List (Fin n)) (hw : w.length ≤ s + 1) :
      Continuous (fun t => q t w) := by
    have he (t : ι) : q t w = p t w :=
      ((hq t).mono (by omega : s + 1 ≤ s + 2)).eq_of_nil_eq (hp t)
        ((hq0 t).trans (hp0 t).symm) w hw
    simpa only [he] using hpc w hw
  have hq1 (t : ι) (i : Fin n) : q t [i] = localizedDirichletPartial K χ (u t) i := by
    have h := hq t [] (by simp) i
    rw [hq0 t] at h
    exact h.unique (localizedDirichletPartial_weak K χ (u t) i)
  have hsource := hG.add (hasContinuousWeakJet_localizedDivergenceCorrection K A hA
    χ hχ hχK u hu)
  obtain ⟨g, hg0, hg, hgc⟩ := hsource
  have hdiv (t : ι) : DivergenceEquation (A t) (fun i => q t [i]) (g t [])
      (cthickening (3 * r) (tsupport χ)) := by
    intro φ _ _
    rw [hg0 t]
    simpa only [hq1 t] using localized_divergence_of_cutoff_tests K (A t) χ
      (hχK.trans interior_subset) (u t) (G t) (heq t) φ
  have hsupport (t : ι) : ∀ᵐ x ∂volume, x ∉ tsupport χ → q t [] x = 0 := by
    rw [hq0 t]
    exact localizedDirichletValue_ae_support K χ (u t)
  refine ⟨q, hq0, hq, ?_⟩
  intro v hv
  cases v with
  | nil => exact hlow [] (by simp)
  | cons i v =>
    cases v with
    | nil => exact hlow [i] (by simp)
    | cons j w =>
      have hw : w.length ≤ s := by simp only [List.length_cons] at hv; omega
      have hcomm (t : ι) := divergence_equation_commuted_of_jets
        (A t) (q t) (g t) (hq t) (hg t) (hdiv t) w hw
      have hc := continuous_commutedSource A g q hA hlow hgc w hw
      apply continuous_iff_continuousAt.mpr
      intro t₀
      apply tendsto_weak_commuted_secondJet_of_divergence A (A t₀) q (q t₀)
        (fun t => commutedSource (A t) (g t) (q t) w)
        (commutedSource (A t₀) (g t₀) (q t₀) w)
        hq (hq t₀) hχ hsupport (hsupport t₀) hr hell hD hEll hAD w hw
        hcomm (hcomm t₀) hc.continuousAt
      · intro k
        exact (hlow (k :: w) (by simp only [List.length_cons]; omega)).continuousAt
      · intro k l
        have hc := (hA k l [] (by simp)).continuousAt (x := t₀)
        simpa only [orderedSchwartzDerivative, multiplier_sub, sub_self] using
          hc.tendsto.sub_const (schwartzMultiplier (A t₀ k l))
      · intro k l
        have hc := (hA k l [l] (by simp)).continuousAt (x := t₀)
        simpa only [orderedSchwartzDerivative, derivative_multiplier_sub, sub_self] using
          hc.tendsto.sub_const
            (schwartzMultiplier (∂_{EuclideanSpace.single l (1 : ℝ)} (A t₀ k l)))

end PoincareConjecture.M35.Uniqueness.Heat
