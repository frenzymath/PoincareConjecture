
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.OperatorReaction.Endomorphism
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.OperatorReaction.Scalar
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.OperatorReaction.Spectral












namespace Poincare.HamiltonIvey

open Set
open scoped BigOperators

noncomputable section

local instance : NormedAddCommGroup ThreeMatrix := Matrix.normedAddCommGroup
local instance : NormedSpace ℝ ThreeMatrix := Matrix.normedSpace

theorem operatorReaction_diagonal (lam mu nu : ℝ) :
    operatorReaction (Poincare.diagonalSpectrum lam mu nu) =
      Poincare.diagonalSpectrum
        (2 * (lam ^ 2 + mu * nu))
        (2 * (mu ^ 2 + lam * nu))
        (2 * (nu ^ 2 + lam * mu)) :=
  operatorReaction_diagonal_entries ![lam, mu, nu]



theorem operator_reaction_invariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hn : Module.finrank ℝ E = 3)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : ℝ → E →ₗ[ℝ] E}
    (hcont : ∀ v : E, ContinuousOn (fun t => A t v) (Set.Icc a b))
    (hsymm : ∀ t ∈ Set.Icc a b, (A t).IsSymmetric)
    (hderiv : ∀ t ∈ Set.Ioo a b, ∀ v : E,
      HasDerivAt (fun s => A s v) (endomorphismReaction (A t) v) t)
    (hinit : A a ∈ region hn a) :
    ∀ t ∈ Set.Icc a b, A t ∈ region hn t := by
  let hAa := hsymm a ⟨le_rfl, hab⟩
  let e := hAa.eigenvectorBasis hn
  let B : ℝ → ThreeMatrix := fun t => LinearMap.toMatrix e.toBasis e.toBasis (A t)
  let d : ℝ → Fin 3 → ℝ := fun t i => B t i i
  have hBc : ContinuousOn B (Icc a b) := continuousOn_operatorMatrix e hcont
  have hBd : ∀ t ∈ Ioo a b, HasDerivAt B (operatorReaction (B t)) t := by
    intro t ht
    simpa only [B, toMatrix_endomorphismReaction] using
      hasDerivAt_operatorMatrix e (hderiv t ht)
  have hBa : B a = Matrix.diagonal (hAa.eigenvalues hn) := by
    simpa [B, e] using hAa.toMatrix_eigenvectorBasis hn
  have hoff := operator_reaction_stays_diagonal hBc hBd (by
    intro i j hij
    simp [hBa, hij])
  have hBdiag : ∀ t ∈ Icc a b, B t = Matrix.diagonal (d t) := by
    intro t ht
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [hij, hoff t ht i j hij]
  have hdc (i : Fin 3) : ContinuousOn (fun t => d t i) (Icc a b) :=
    (continuousOn_pi.mp (continuousOn_pi.mp hBc i) i)
  have hdd : ∀ t ∈ Ioo a b, ∀ i,
      HasDerivAt (fun s => d s i)
        (![2 * (d t 0 ^ 2 + d t 1 * d t 2),
          2 * (d t 1 ^ 2 + d t 0 * d t 2),
          2 * (d t 2 ^ 2 + d t 0 * d t 1)] i) t := by
    intro t ht i
    have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hBd t ht) i) i
    rw [hBdiag t (Ioo_subset_Icc_self ht), operatorReaction_diagonal_entries] at h
    simpa only [Matrix.diagonal_apply_eq] using h
  have hda (i : Fin 3) : d a i = hAa.eigenvalues hn i := by
    simp [d, hBa]
  have horder : d a 1 ≤ d a 0 ∧ d a 2 ≤ d a 1 := by
    simp only [hda]
    exact ⟨hAa.eigenvalues_antitone hn (by decide), hAa.eigenvalues_antitone hn (by decide)⟩
  have heigen : ∀ t ∈ Icc a b, ∀ i, A t (e i) = d t i • e i := by
    intro t ht i
    apply e.toBasis.repr.injective
    ext j
    have h := congrFun (congrFun (hBdiag t ht) j) i
    by_cases hij : i = j
    · subst j
      simpa [B, LinearMap.toMatrix_apply] using h
    · simpa [B, LinearMap.toMatrix_apply, hij, Ne.symm hij] using h
  have hscalarInit : (d a 0 + d a 1 + d a 2, max (-d a 2) 0) ∈ scalarRegion a := by
    have hi := (mem_region_iff_diagonal hn hAa e (heigen a ⟨le_rfl, hab⟩)
      (fun i j hij => by simpa only [hda] using hAa.eigenvalues_antitone hn hij) a).mp hinit
    simpa [Fin.sum_univ_succ, add_assoc] using hi
  have hpersist := reaction_two_invariance ha hab (hdc 0) (hdc 1) (hdc 2)
    (fun t ht => hdd t ht 0) (fun t ht => hdd t ht 1) (fun t ht => hdd t ht 2)
    horder hscalarInit
  have hordered := reaction_two_order hab (hdc 0) (hdc 1) (hdc 2)
    (fun t ht => hdd t ht 0) (fun t ht => hdd t ht 1) (fun t ht => hdd t ht 2) horder
  intro t ht
  apply (mem_region_iff_diagonal hn (hsymm t ht) e (heigen t ht) ?_ t).mpr
  · simpa [Fin.sum_univ_succ, add_assoc] using hpersist t ht
  · intro i j hij
    have ho := hordered t ht
    fin_cases i <;> fin_cases j <;>
      first | exact le_rfl | exact ho.1 | exact ho.2 | exact ho.2.trans ho.1 |
        norm_num [Fin.le_def] at hij

end

end Poincare.HamiltonIvey
