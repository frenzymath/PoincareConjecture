import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalNonautonomous
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalFormOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

local instance principalContinuousGraphNormed (K : Set V) :
    NormedAddCommGroup (dirichletForm K) :=
  inferInstanceAs (NormedAddCommGroup (dirichletImage K).range.topologicalClosure)

local instance principalContinuousGraphSpace (K : Set V) : NormedSpace ℝ (dirichletForm K) :=
  inferInstanceAs (NormedSpace ℝ (dirichletImage K).range.topologicalClosure)

local instance principalContinuousOperatorNormed (K : Set V) :
    NormedAddCommGroup (dirichletForm K →L[ℝ] dirichletForm K) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance principalContinuousOperatorSpace (K : Set V) :
    NormedSpace ℝ (dirichletForm K →L[ℝ] dirichletForm K) :=
  ContinuousLinearMap.toNormedSpace

theorem exists_small_initial_interval {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hc : ContinuousOn f (Icc 0 b)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ < b ∧ ∀ t ∈ Icc 0 τ, ‖f t - f 0‖ ≤ ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hc 0 ⟨le_rfl, hb.le⟩) ε hε
  let τ := min (b / 2) (min (δ / 2) 1)
  have hτ : 0 < τ := lt_min (by linarith) (lt_min (by linarith) zero_lt_one)
  have hτ1 : τ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hτb : τ < b := (min_le_left _ _).trans_lt (by linarith)
  have hτδ : τ < δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  refine ⟨τ, hτ, hτ1, hτb, ?_⟩
  intro t ht
  have htb : t ∈ Icc 0 b := ⟨ht.1, ht.2.trans hτb.le⟩
  have htd : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hτδ
  simpa only [dist_eq_norm] using (hclose htb htd).le

private theorem principal_difference_pairing (K : Set V)
    (A B : Fin n → Fin n → 𝓢(V, ℝ)) (w v P : dirichletForm K) :
    inner ℝ w ((principalFormOperator K A - principalFormOperator K B) v + P) -
        principalEnergy K A w v = inner ℝ w P - principalEnergy K B w v := by
  simp only [sub_apply, inner_add_right, inner_sub_right,
    principalFormOperator_pairing]
  ring

private theorem principal_interval_bound (K : Set V)
    (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ)) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc 0 b)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ < b ∧
      AEStronglyMeasurable (fun t => principalFormOperator K (A 0) - principalFormOperator K (A t))
        (timeMeasure τ) ∧
      ∀ᵐ t ∂timeMeasure τ, ‖principalFormOperator K (A 0) - principalFormOperator K (A t)‖ ≤ ε := by
  let : SecondCountableTopologyEither ℝ (dirichletForm K →L[ℝ] dirichletForm K) :=
    ⟨Or.inl inferInstance⟩
  have hnorm : ContinuousOn (fun t =>
      ‖principalFormOperator K (A t) - principalFormOperator K (A 0)‖) (Icc 0 b) :=
    (hc.sub continuousOn_const).norm
  refine (exists_small_initial_interval
    (fun t => ‖principalFormOperator K (A t) - principalFormOperator K (A 0)‖) hb hε hnorm).elim ?_
  intro τ h
  have hRc : ContinuousOn
      (fun t => principalFormOperator K (A 0) - principalFormOperator K (A t)) (Icc 0 τ) :=
    continuousOn_const.sub (hc.mono (Icc_subset_Icc le_rfl h.2.2.1.le))
  refine ⟨τ, h.1, h.2.1, h.2.2.1,
    (hRc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [sub_self, norm_zero, sub_zero, norm_norm, norm_sub_rev]
    using h.2.2.2 t (Ioc_subset_Icc_self ht)

theorem exists_continuous_principal_heat {K : Set V} (hK : IsCompact K)
    (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ)) {ell : ℝ} (hEll : 0 < ell)
    (hA : ∀ i j x, A 0 i j x = A 0 j i x)
    (hell : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 i j x * ξ i * ξ j)
    {b : ℝ} (hb : 0 < b)
    (hc : ContinuousOn (fun t => principalFormOperator K (A t)) (Icc 0 b)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ < b ∧
      ∀ P : ℝ → dirichletForm K, MemLp P 2 (timeMeasure τ) →
      ∃ (v : ℝ → dirichletForm K) (U : ℝ → dirichletValue K),
        MemLp v 2 (timeMeasure τ) ∧ U 0 = 0 ∧ ContinuousOn U (Icc 0 τ) ∧
        (∀ᵐ t ∂timeMeasure τ, dirichletInclusion K (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure τ, ∀ w : dirichletForm K,
          HasDerivWithinAt (fun s => inner ℝ (dirichletInclusion K w) (U s))
            (inner ℝ w (P t) - principalEnergy K (A t) w (v t)) (Icc 0 τ) t) := by
  refine (exists_principal_nonautonomous_tolerance hK (A 0) hEll hA hell).elim ?_
  intro ε hε
  refine (principal_interval_bound K A hb hε.1 hc).elim ?_
  intro τ hτ
  let R : ℝ → dirichletForm K →L[ℝ] dirichletForm K := fun t =>
    principalFormOperator K (A 0) - principalFormOperator K (A t)
  refine ⟨τ, hτ.1, hτ.2.1, hτ.2.2.1, ?_⟩
  intro P hP
  obtain ⟨v, U, hv, hU0, hUc, hUv, hweak⟩ :=
    hε.2 τ hτ.1.le hτ.2.1 R hτ.2.2.2.1 hτ.2.2.2.2 P hP
  refine ⟨v, U, hv, hU0, hUc, hUv, ?_⟩
  filter_upwards [hweak] with t ht
  intro w
  have he := principal_difference_pairing K (A 0) (A t) w (v t) (P t)
  have h := ht w
  change HasDerivWithinAt _
    (inner ℝ w ((principalFormOperator K (A 0) - principalFormOperator K (A t)) (v t) + P t) -
      principalEnergy K (A 0) w (v t)) _ _ at h
  rw [he] at h
  exact h

end PoincareConjecture.M35.Uniqueness.Heat
