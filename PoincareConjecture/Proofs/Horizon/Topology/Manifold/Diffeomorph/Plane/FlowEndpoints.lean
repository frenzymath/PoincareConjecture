import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.FlowCoordinates








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Manifold

namespace Poincare.Manifold.PlaneDiffeomorph

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "v₀" => (!₂[(1 : ℝ), 0] : E₂)



theorem flow_coordinates_eq_diffeomorph
    (g : Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞) {L : ℝ}
    (hsection : ∀ y, g (!₂[L, y]) = !₂[L, y])
    {Φ : ℝ → E₂ → E₂} (hinit : ∀ x, Φ 0 x = x)
    (hflow : ∀ x t, HasDerivAt (fun s => Φ s x)
      (fderiv ℝ g (g.symm (Φ t x)) v₀) t) :
    ∀ x : E₂, Φ (x 0 - L) (!₂[L, x 1]) = g x := by
  have hg : ContDiff ℝ ∞ g := g.contMDiff.contDiff
  have hgi : ContDiff ℝ ∞ g.symm := g.symm.contMDiff.contDiff
  let V : E₂ → E₂ := fun x => fderiv ℝ g (g.symm x) v₀
  have hV : ContDiff ℝ ∞ V :=
    ((hg.fderiv_right (by simp)).comp hgi).clm_apply contDiff_const
  intro x
  let a : E₂ := !₂[L, x 1]
  have hη (t : ℝ) : HasDerivAt (fun s => g (a + s • v₀))
      (V (g (a + t • v₀))) t := by
    have hd := (hg.differentiable (by simp) (a + t • v₀)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v₀).const_add a)
    simpa only [V, g.symm_apply_apply, one_smul, Function.comp_def, id_eq] using hd
  have heq := Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
    isOpen_univ isPreconnected_univ
    (fun t _ => ⟨mem_univ _, hflow a t⟩)
    (fun t _ => ⟨mem_univ _, hη t⟩)
    (a := 0) (mem_univ _) (by simp [a, hinit, hsection])
  have hpoint : a + (x 0 - L) • v₀ = x := by
    ext i
    fin_cases i <;> simp [a]
  simpa only [hpoint] using heq (mem_univ (x 0 - L))



theorem flow_coordinates_eq_self_of_exterior
    {V : E₂ → E₂} (hV : ContDiff ℝ ∞ V) {L B T : ℝ}
    (hfix : ∀ x : E₂, x 0 ≤ L ∨ x 1 ≤ B ∨ T ≤ x 1 → V x = v₀)
    {Φ : ℝ → E₂ → E₂} (hinit : ∀ x, Φ 0 x = x)
    (hflow : ∀ x t, HasDerivAt (fun s => Φ s x) (V (Φ t x)) t)
    {x : E₂} (hx : x 0 ≤ L ∨ x 1 ≤ B ∨ T ≤ x 1) :
    Φ (x 0 - L) (!₂[L, x 1]) = x := by
  let a : E₂ := !₂[L, x 1]
  rcases hx with hx | hx
  · have hback := Poincare.ODE.Plane.eq_horizontal_backward_ray hV (hflow a)
      (fun y hy => hfix y (Or.inl hy))
      (a := 0) (by simp [hinit, a] : Φ 0 a 0 ≤ L)
      (L - x 0) (sub_nonneg.mpr hx)
    calc
      Φ (x 0 - L) a = a - (L - x 0) • v₀ := by
        simpa only [zero_sub, neg_sub, hinit] using hback
      _ = x := by ext i; fin_cases i <;> simp [a]
  · have hη (t : ℝ) : HasDerivAt (fun s => a + s • v₀) (V (a + t • v₀)) t := by
      rw [hfix _ (Or.inr (by simpa [a] using hx))]
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v₀).const_add a
    have heq := Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
      isOpen_univ isPreconnected_univ
      (fun t _ => ⟨mem_univ _, hflow a t⟩)
      (fun t _ => ⟨mem_univ _, hη t⟩)
      (a := 0) (mem_univ _) (by simp [hinit])
    have hpoint : a + (x 0 - L) • v₀ = x := by
      ext i
      fin_cases i <;> simp [a]
    simpa only [hpoint] using heq (mem_univ (x 0 - L))

end Poincare.Manifold.PlaneDiffeomorph
