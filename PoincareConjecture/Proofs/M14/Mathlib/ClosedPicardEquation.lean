import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathPrimitive
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathSubstitution










set_option autoImplicit false

open Set
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}



theorem closedPath_picard_equation_of_ode (t₀ : Icc a b) (f : ℝ × E → E)
    (hf : ContinuousOn f (Icc a b ×ˢ univ)) (φ : C(Icc a b, E))
    (hode : ∀ r : Icc a b, HasDerivWithinAt
      (fun s => φ (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (f (r.val, φ r)) (Icc a b) r.val) :
    φ = ContinuousMap.const _ (φ t₀) + closedPathPrimitive t₀ (closedTimePostcomp f hf φ) := by
  let π : C(ℝ, Icc a b) := ⟨projIcc a b (t₀.property.1.trans t₀.property.2), continuous_projIcc⟩
  let γ : C(ℝ, E) := φ.comp π
  let g : C(ℝ, E) := (closedTimePostcomp f hf φ).comp π
  ext r
  have hderiv (s : ℝ) (hs : s ∈ Ioo (min t₀.val r.val) (max t₀.val r.val)) :
      HasDerivWithinAt γ (g s) (Ioi s) s := by
    have hsab : s ∈ Ioo a b :=
      ⟨(le_min t₀.property.1 r.property.1).trans_lt hs.1,
        hs.2.trans_le (max_le t₀.property.2 r.property.2)⟩
    have hπ : π s = ⟨s, Ioo_subset_Icc_self hsab⟩ :=
      projIcc_of_mem (t₀.property.1.trans t₀.property.2) (Ioo_subset_Icc_self hsab)
    have hg : g s = f (s, φ ⟨s, Ioo_subset_Icc_self hsab⟩) := by
      change f ((π s).val, φ (π s)) = _
      rw [hπ]
    rw [hg]
    exact ((hode ⟨s, Ioo_subset_Icc_self hsab⟩).hasDerivAt
      (Icc_mem_nhds hsab.1 hsab.2)).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right γ.continuous.continuousOn
    hderiv (g.continuous.intervalIntegrable t₀.val r.val)
  have hπr : π r.val = r := projIcc_of_mem (t₀.property.1.trans t₀.property.2) r.property
  have hπ₀ : π t₀.val = t₀ := projIcc_of_mem (t₀.property.1.trans t₀.property.2) t₀.property
  change (∫ s in t₀.val..r.val, g s) = φ (π r.val) - φ (π t₀.val) at hFTC
  rw [hπr, hπ₀] at hFTC
  change φ r = φ t₀ + closedPathPrimitive t₀ (closedTimePostcomp f hf φ) r
  rw [closedPathPrimitive_apply]
  change φ r = φ t₀ + ∫ s in t₀.val..r.val, g s
  rw [hFTC, add_sub_cancel]




theorem closedPath_ode_of_picard_equation (t₀ : Icc a b) (f : ℝ × E → E)
    (hf : ContinuousOn f (Icc a b ×ˢ univ)) (x₀ : E) (φ : C(Icc a b, E))
    (heq : φ = ContinuousMap.const _ x₀ + closedPathPrimitive t₀ (closedTimePostcomp f hf φ)) :
    φ t₀ = x₀ ∧ ∀ r : Icc a b, HasDerivWithinAt
      (fun s => φ (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (f (r.val, φ r)) (Icc a b) r.val := by
  constructor
  · have hi := congrArg (fun v : C(Icc a b, E) => v t₀) heq
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
      closedPathPrimitive_initial, add_zero] using hi
  · intro r
    have hd := (hasDerivWithinAt_const r.val (Icc a b) x₀).add
      (closedPathPrimitive_hasDerivWithinAt t₀ r (closedTimePostcomp f hf φ))
    change HasDerivWithinAt
      (fun s => x₀ + closedPathPrimitive t₀ (closedTimePostcomp f hf φ)
        (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (0 + f (r.val, φ r)) (Icc a b) r.val at hd
    rw [zero_add] at hd
    apply hd.congr_of_mem _ r.property
    intro s _
    exact congrArg (fun v : C(Icc a b, E) =>
      v (projIcc a b (t₀.property.1.trans t₀.property.2) s)) heq

end PoincareConjecture.M14
