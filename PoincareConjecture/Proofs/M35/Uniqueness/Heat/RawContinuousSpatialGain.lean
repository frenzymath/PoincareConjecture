import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousLowerSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ContinuousEllipticGain
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawMixedCoefficientJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialCoefficientBound
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.RawUniformRestart
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.VectorDivergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Metric
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure X)

theorem raw_form_heat_continuous_spatial_gain {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (time : ι → Icc a b) (htime : Continuous time)
    (u w : ι → PiLp 2 (fun _ : Fin n => dirichletForm K)) {s : ℕ}
    (hu : ∀ k, HasContinuousInteriorJets K (fun t => u t k) (s + 1))
    (hw : ∀ k, HasContinuousInteriorJets K (fun t => w t k) s)
    (heq : ∀ t, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (w t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection (time t)) hK.isClosed η hη (u t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (time t)) η hη)
                z (u t)) (k : Fin n) :
    HasContinuousInteriorJets K (fun t => u t k) (s + 2) := by
  let A := fun t => rawCutoffPrincipalCoefficient (F.metric (time t)) η hη
  let B := fun t => rawCutoffFirstComponent (F.connection (time t)) η hη
  let C := fun t => rawCutoffZeroComponent (F.connection (time t)) η hη
  have hAc (i j : Fin n) (v : List (Fin n)) : Continuous (fun t =>
      schwartzMultiplier (orderedSchwartzDerivative v (A t i j))) :=
    ((contDiffOn_rawPrincipal_mixed_multiplier F hab hJ η hη 0 i j v).continuousOn.domRestrict).comp
      htime
  have hBc (i j l : Fin n) (v : List (Fin n)) : Continuous (fun t =>
      schwartzMultiplier (orderedSchwartzDerivative v (B t i j l))) :=
    ((contDiffOn_rawFirst_mixed_multiplier F hab hJ η hη 0 i j l v).continuousOn.domRestrict).comp
      htime
  have hCc (i j : Fin n) (v : List (Fin n)) : Continuous (fun t =>
      schwartzMultiplier (orderedSchwartzDerivative v (C t i j))) :=
    ((contDiffOn_rawZero_mixed_multiplier F hab hJ η hη 0 i j v).continuousOn.domRestrict).comp
      htime
  intro χ hχ hχK
  let G : ι → L2 := fun t => schwartzMultiplier χ
    ((rawLowerFormOperator (F.connection (time t)) hK.isClosed η hη (u t) k : L2) -
      (dirichletInclusion K (w t k) : L2))
  have hG : HasContinuousWeakJet G s := by
    have hlow := hasContinuousWeakJet_localized_vector_lowerOrder hK.isClosed B C
      (fun i j l v _ => hBc i j l v) (fun i j v _ => hCc i j v) u hu χ hχ hχK k
    simpa only [G, B, C, rawLowerFormOperator, map_sub, localizedDirichletValue] using
      hlow.sub (hw k χ hχ hχK)
  have htest (t : ι) (φ : 𝓢(X, ℝ)) : principalEnergy K (A t) (u t k)
      (intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
        inner ℝ (G t) (φ.toLp 2 volume) := by
    have h := vector_component_divergence K (A t)
      (rawCutoffPrincipalCoefficient_symmetric (F.metric (time t)) η hη) (u t)
      (rawLowerFormOperator (F.connection (time t)) hK.isClosed η hη (u t))
      (finiteHilbertMap (dirichletInclusion K) (w t)) (heq t) k
      (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)
    change principalEnergy K (A t) (u t k)
      (intoDirichletForm K (cutoffSupportedTest K χ (hχK.trans interior_subset) φ)) =
        inner ℝ ((rawLowerFormOperator (F.connection (time t)) hK.isClosed η hη (u t) k : L2) -
          (dirichletInclusion K (w t k) : L2)) ((schwartzProduct χ φ).toLp 2 volume) at h
    rw [schwartzProduct_toLp, ← schwartzMultiplier_selfAdjoint] at h
    exact h
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
  exact hasContinuousWeakJet_of_cutoff_tests K A (fun i j v _ => hAc i j v)
    χ hχ hχK (fun t => u t k) (hu k) G hG htest hr hell hD
    (fun t x hx => hEll (time t) (time t).property x (hthick hx))
    (fun t => hAD (time t) (time t).property)

theorem raw_form_heat_continuous_third_jets {J : Set ℝ} (F : RicciFlow n X J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set X} (hK : IsCompact K)
    (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (time : ι → Icc a b) (htime : Continuous time)
    (u w : ι → PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hu : Continuous u) (hw : Continuous w)
    (heq : ∀ t, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (w t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection (time t)) hK.isClosed η hη (u t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (time t)) η hη)
                z (u t)) (k : Fin n) :
    HasContinuousInteriorJets K (fun t => u t k) 3 := by
  have hu1 (j : Fin n) : HasContinuousInteriorJets K (fun t => u t j) 1 :=
    hasContinuousInteriorJets_one _
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => dirichletForm K) j).continuous.comp hu)
  have hw1 (j : Fin n) : HasContinuousInteriorJets K (fun t => w t j) 1 :=
    hasContinuousInteriorJets_one _
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => dirichletForm K) j).continuous.comp hw)
  have hu2 (j : Fin n) : HasContinuousInteriorJets K (fun t => u t j) 2 :=
    raw_form_heat_continuous_spatial_gain F hab hJ hK η hη hηK time htime u w hu1
      (fun l => (hw1 l).mono (by omega)) heq j
  exact raw_form_heat_continuous_spatial_gain F hab hJ hK η hη hηK time htime u w hu2 hw1 heq k

end PoincareConjecture.M35.Uniqueness.Heat
