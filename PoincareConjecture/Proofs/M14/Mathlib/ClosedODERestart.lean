import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyRestart
import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEJointFamily
import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEUniqueness

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem closedODE_exists_restart_family {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → E)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ c d : ℝ, ∃ t₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ t₁.val = t₀.val ∧ Icc c d ∈ 𝓝[Icc a b] t₀.val ∧
      ∃ γ : ℝ → E, γ t₀.val = x₀ ∧ ContDiffOn ℝ ∞ γ (Icc c d) ∧
        (∀ s ∈ Icc c d, γ s ∈ U ∧
          HasDerivWithinAt γ (f (s, γ s)) (Icc c d) s) ∧
        ∀ᶠ r in 𝓝[Icc c d] t₀.val,
          ∃ V : Set E, IsOpen V ∧ γ r ∈ V ∧ ∃ β : E × ℝ → E,
            ContDiffOn ℝ ∞ β (V ×ˢ Icc c d) ∧ ∀ y ∈ V,
              β (y, r) = y ∧ ∀ s ∈ Icc c d,
                β (y, s) ∈ U ∧ HasDerivWithinAt (fun t => β (y, t))
                  (f (s, β (y, s))) (Icc c d) s := by
  obtain ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, ρ, hρ, α, hα, hdata⟩ :=
    closedODE_exists_joint_family hab t₀ hU f hf hx₀
  have hx : x₀ ∈ ball x₀ ρ := mem_ball_self hρ
  have ht : t₀.val ∈ Icc c d := hi ▸ t₁.property
  have hinit (x : E) (hx' : x ∈ ball x₀ ρ) : α (x, t₀.val) = x :=
    hi ▸ (hdata x hx').1
  have hbij := closedFamily_eventually_bijective_sliceDerivative
    (uniqueDiffOn_Icc hcd) isOpen_ball α hα hx ht hinit
  refine ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, fun s => α (x₀, s), hinit x₀ hx,
    hα.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hs => ⟨hx, hs⟩),
    (hdata x₀ hx).2, ?_⟩
  filter_upwards [hbij, self_mem_nhdsWithin] with r hr hrC
  obtain ⟨V, hV, hcenter, β, hβ, hβdata⟩ :=
    closedFamily_restart_of_bijective isOpen_ball α hα hx hrC hr
  refine ⟨V, hV, hcenter, β, hβ, ?_⟩
  intro y hy
  obtain ⟨hstart, x, hx', heq⟩ := hβdata y hy
  refine ⟨hstart, ?_⟩
  intro s hs
  have heqfun : (fun t => β (y, t)) = fun t => α (x, t) := funext heq
  rw [heqfun, heq s]
  exact (hdata x hx').2 s hs

theorem closedODE_exists_restart_along {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → E)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) (γ : ℝ → E)
    (hγ : ∀ s ∈ Icc a b, HasDerivWithinAt γ (f (s, γ s)) (Icc a b) s)
    (hx₀ : γ t₀.val ∈ U) :
    ∃ c d : ℝ, ∃ t₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ t₁.val = t₀.val ∧ Icc c d ∈ 𝓝[Icc a b] t₀.val ∧
        ∀ᶠ r in 𝓝[Icc c d] t₀.val,
          ∃ V : Set E, IsOpen V ∧ γ r ∈ V ∧ ∃ β : E × ℝ → E,
            ContDiffOn ℝ ∞ β (V ×ˢ Icc c d) ∧ ∀ y ∈ V,
              β (y, r) = y ∧ ∀ s ∈ Icc c d,
                β (y, s) ∈ U ∧ HasDerivWithinAt (fun t => β (y, t))
                  (f (s, β (y, s))) (Icc c d) s := by
  obtain ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, η, hinit, _, hη, hrest⟩ :=
    closedODE_exists_restart_family hab t₀ hU f hf hx₀
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have heq : EqOn η γ (Icc c d) :=
    closedODE_interval_solution_unique hcd hU f (hf.mono (prod_mono hsub Subset.rfl))
      (fun _ hs => (hη _ hs).1) (fun _ hs => (hη _ hs).2)
      (fun s hs => (hγ s (hsub hs)).mono hsub) (hi ▸ t₁.property) hinit
  refine ⟨c, d, t₁, hcd, hac, hdb, hi, hnear, ?_⟩
  filter_upwards [hrest, self_mem_nhdsWithin] with r hr hrC
  rwa [heq hrC] at hr

end PoincareConjecture.M14
