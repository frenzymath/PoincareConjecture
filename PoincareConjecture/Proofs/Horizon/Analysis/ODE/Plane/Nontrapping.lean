import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Plane.NoReturn

open Set
open scoped ContDiff

namespace Poincare.ODE.Plane

theorem not_isBounded_forward_orbit
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : ∀ t, 0 ≤ t → HasDerivAt γ (V (γ t)) t) :
    ¬ Bornology.IsBounded (γ '' Ici 0) := by
  intro hbounded
  obtain ⟨W, hW, hWne, hWV, S, v, hS, hfix⟩ :=
    exists_nonvanishing_compact_modification hV hne hbounded.isCompact_closure
  have hγW (t : ℝ) (ht : 0 ≤ t) : HasDerivAt γ (W (γ t)) t := by
    rw [hWV (subset_closure (mem_image_of_mem γ ht))]
    exact hγ t ht
  obtain ⟨β, hβ0, hβ⟩ :=
    Poincare.ODE.exists_global_solution_of_eq_const_off_compact hW hS hfix (γ 0)
  have heq (t : ℝ) (ht : 0 ≤ t) : β t = γ t := by
    have h := Poincare.ODE.eqOn_Icc_of_hasDerivAt (hW.of_le (by simp))
      (fun s (_ : s ∈ Icc 0 t) => hβ s)
      (fun s hs => hγW s hs.1) hβ0
    exact h ⟨ht, le_rfl⟩
  apply not_isBounded_global_integralCurve hW hWne hβ
  apply hbounded.subset
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, ht, (heq t ht).symm⟩

end Poincare.ODE.Plane
