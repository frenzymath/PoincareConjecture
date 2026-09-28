import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.PrincipalDynamics
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.TimeSegmentsEquation

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

theorem principalValueHeat_join (K : Set V) (A : ℝ → Fin n → Fin n → 𝓢(V, ℝ))
    (L : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K)) {r S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hAc : ContinuousOn (fun t => principalFormOperator K (A (r + t))) (Icc 0 (S + T)))
    (hLc : ContinuousOn (fun t => L (r + t)) (Icc 0 (S + T)))
    {u₀ : PiLp 2 (fun _ : Fin m => dirichletValue K)}
    {v₁ v₂ : ℝ → PiLp 2 (fun _ : Fin m => dirichletForm K)}
    {U₁ U₂ : ℝ → PiLp 2 (fun _ : Fin m => dirichletValue K)}
    (h₁ : PrincipalValueHeat K A L r S u₀ v₁ U₁)
    (h₂ : PrincipalValueHeat K A L (r + S) T (U₁ S) v₂ U₂) :
    PrincipalValueHeat K A L r (S + T) u₀ (joinTime v₁ v₂ S) (joinTime U₁ U₂ S) := by
  obtain ⟨hv₁, hU₁0, hU₁c, hgraph₁, _, heq₁⟩ := h₁
  obtain ⟨hv₂, hU₂0, hU₂c, hgraph₂, _, heq₂⟩ := h₂
  have hv := memLp_joinTime hS hT hv₁ hv₂
  have hU0 : joinTime U₁ U₂ S 0 = u₀ := by simp only [joinTime, if_pos hS, hU₁0]
  have hUc := continuousOn_joinTime hU₁c hU₂c hU₂0.symm
  have hgraph := ae_graph_joinTime (finiteHilbertMap (dirichletInclusion K)) hgraph₁ hgraph₂
  apply principalValueHeat_of_integral K A L (add_nonneg hS hT) hAc hLc hv hU0 hUc hgraph
  intro t ht w
  have hsub : Icc (0 : ℝ) S ⊆ Icc 0 (S + T) :=
    Icc_subset_Icc le_rfl (le_add_of_nonneg_right hT)
  have hshift : MapsTo (fun s : ℝ => S + s) (Icc 0 T) (Icc 0 (S + T)) := by
    intro s hs
    constructor <;> linarith only [hS, hs.1, hs.2]
  have hA₂ : ContinuousOn (fun s => principalFormOperator K (A ((r + S) + s)))
      (Icc 0 T) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, add_assoc] using
      hAc.comp (continuous_const.add continuous_id).continuousOn hshift
  have hL₂ : ContinuousOn (fun s => L ((r + S) + s)) (Icc 0 T) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq, add_assoc] using
      hLc.comp (continuous_const.add continuous_id).continuousOn hshift
  have hf := principalHeat_integrand_memLp K A L (hAc.mono hsub) (hLc.mono hsub) hv₁ w
  have hg := principalHeat_integrand_memLp K A L hA₂ hL₂ hv₂ w
  exact joinTime_integral_equation
    (fun u => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) u)
    (fun s v => inner ℝ (finiteHilbertMap (dirichletInclusion K) w) (L s v) -
      principalVectorEnergy K (A s) w v) hS hT
    (fun s hs => heq₁ s hs w) (fun s hs => heq₂ s hs w)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hS).mpr (hf.integrable (by norm_num)))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hg.integrable (by norm_num))) t ht

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
