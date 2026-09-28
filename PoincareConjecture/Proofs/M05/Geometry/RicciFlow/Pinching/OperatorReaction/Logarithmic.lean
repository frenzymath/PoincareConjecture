
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.OperatorReaction
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Persistence










namespace Poincare.HamiltonIvey

open scoped BigOperators



theorem operator_reaction_logarithmic_pinching
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : ℝ → E →ₗ[ℝ] E}
    (hcont : ∀ v : E, ContinuousOn (fun t => A t v) (Set.Icc a b))
    (hsymm : ∀ t ∈ Set.Icc a b, (A t).IsSymmetric)
    (hderiv : ∀ t ∈ Set.Ioo a b, ∀ v : E,
      HasDerivAt (fun s => A s v) (endomorphismReaction (A t) v) t)
    (hinit : A a ∈ region hn a) :
    ∀ t (ht : t ∈ Set.Icc a b),
      let X := max (-(hsymm t ht).eigenvalues hn 2) 0
      0 < X → 2 * X * (Real.log X + Real.log (1 + t) - 3) ≤
        2 * LinearMap.trace ℝ E (A t) := by
  have hpres := operator_reaction_invariance hn ha hab hcont hsymm hderiv hinit
  intro t ht X hX
  obtain ⟨hA, hmem⟩ := hpres t ht
  have htrace := hA.trace_eq_sum_eigenvalues hn
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    RCLike.ofReal_real_eq_id, id_eq] at htrace
  have h := PoincareConjecture.logarithmic_pinching_of_scalar_region (ha.trans ht.1)
    (hA.eigenvalues_antitone hn (by decide : (0 : Fin 3) ≤ 1))
    (hA.eigenvalues_antitone hn (by decide : (1 : Fin 3) ≤ 2))
    (by simpa only [htrace, add_assoc] using hmem) hX
  simpa only [X, htrace, add_assoc] using h

end Poincare.HamiltonIvey
