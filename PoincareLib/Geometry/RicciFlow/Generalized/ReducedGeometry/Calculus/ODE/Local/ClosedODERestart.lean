import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Families.ClosedFamilyRestart
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Families.ClosedODEJointFamily
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Local.ClosedODEUniqueness

/-!
# Actual closed ODE restarts on a common interval

Morgan-Tian Lemma 6.18, pp. 113-114. A jointly smooth local
family and its invertible fixed-time phase maps give restarts at
all nearby closed times. The same retained interval works for all
these restarts, including physical endpoints.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareMT.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth actual ODE has a central solution and nearby-time
restarts on a common relative closed neighborhood. Each restart
retains its actual within equation and state range, the uniform
continuation input of Lemma 6.18, pp. 113-114. -/
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

/-- A supplied actual solution determines the centers of the common
restart neighborhoods by closed-interval uniqueness. The retained
time neighborhood does not depend on the chosen nearby restart time,
as required in Lemma 6.18, pp. 113-114. -/
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

end PoincareMT.M14
