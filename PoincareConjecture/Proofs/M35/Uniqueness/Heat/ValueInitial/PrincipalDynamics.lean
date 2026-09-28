import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.SegmentDynamics









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def principalHeatSource (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) (t : ℝ) :
    PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletForm K) :=
  (finiteHilbertMap (dirichletInclusion K)).adjoint.comp (L t) -
    finiteHilbertMap (principalFormOperator K (A t))

theorem principalHeatSource_pairing (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) (t : ℝ)
    (w v : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    inner ℝ w (principalHeatSource K A L t v) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L t v) -
        principalVectorEnergy K (A t) w v := by
  simp only [principalHeatSource, sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right, principalVectorEnergy_pairing]

theorem principalHeatSource_memLp (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {r T : ℝ}
    (hAc : ContinuousOn (fun t => principalFormOperator K (A (r + t))) (Icc 0 T))
    (hLc : ContinuousOn (fun t => L (r + t)) (Icc 0 T))
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)} (hv : MemLp v 2 (timeMeasure T)) :
    MemLp (fun t => principalHeatSource K A L (r + t) (v t)) 2 (timeMeasure T) := by
  apply memLp_continuous_operator _ _ hv
  exact (continuousOn_const.clm_comp hLc).sub
    (finiteHilbertMapOperator.continuous.comp_continuousOn hAc)

theorem principalHeat_integrand_memLp (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {r T : ℝ}
    (hAc : ContinuousOn (fun t => principalFormOperator K (A (r + t))) (Icc 0 T))
    (hLc : ContinuousOn (fun t => L (r + t)) (Icc 0 T))
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)} (hv : MemLp v 2 (timeMeasure T))
    (w : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    MemLp (fun t => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L (r + t) (v t)) -
      principalVectorEnergy K (A (r + t)) w (v t)) 2 (timeMeasure T) := by
  have h := (innerSL ℝ w).comp_memLp' (principalHeatSource_memLp K A L hAc hLc hv)
  change MemLp (fun t => inner ℝ w (principalHeatSource K A L (r + t) (v t)))
    2 (timeMeasure T) at h
  simpa only [principalHeatSource_pairing] using h

theorem principalValueHeat_of_integral (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {r T : ℝ} (hT : 0 ≤ T)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A (r + t))) (Icc 0 T))
    (hLc : ContinuousOn (fun t => L (r + t)) (Icc 0 T))
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (hv : MemLp v 2 (timeMeasure T)) (hU0 : U 0 = u₀) (hUc : ContinuousOn U (Icc 0 T))
    (hgraph : ∀ᵐ t ∂timeMeasure T, finiteHilbertMap (dirichletInclusion K) (v t) = U t)
    (heq : ∀ t ∈ Icc 0 T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U t) =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) w) u₀ +
        ∫ s in (0 : ℝ)..t, inner ℝ (finiteHilbertMap (dirichletInclusion K) w)
          (L (r + s) (v s)) - principalVectorEnergy K (A (r + s)) w (v s)) :
    PrincipalValueHeat K A L r T u₀ v U := by
  have hD := principalHeatSource_memLp K A L hAc hLc hv
  have heq' : ∀ t ∈ Icc 0 T, ∀ w : PiLp 2 (fun _ : Fin m => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (U t) =
        inner ℝ (finiteHilbertMap (dirichletInclusion K) w) u₀ +
          ∫ s in (0 : ℝ)..t, inner ℝ w (principalHeatSource K A L (r + s) (v s)) := by
    simpa only [principalHeatSource_pairing] using heq
  refine ⟨hv, hU0, hUc, hgraph, ?_, heq⟩
  simpa only [principalHeatSource_pairing] using
    tested_integral_hasDeriv (finiteHilbertMap (dirichletInclusion K)) hT hD heq'

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
