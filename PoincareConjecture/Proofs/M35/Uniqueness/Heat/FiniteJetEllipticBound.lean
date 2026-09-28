import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFiniteJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter Metric
open scoped SchwartzMap LineDeriv Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem divergence_equation_commuted_of_jets
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (q g : List (Fin n) → L2) {s : ℕ}
    (hq : IsWeakSchwartzJet q (s + 2)) (hg : IsWeakSchwartzJet g s) {U : Set V}
    (heq : DivergenceEquation A (fun i => q [i]) (g []) U)
    (w : List (Fin n)) (hw : w.length ≤ s) :
    DivergenceEquation A (fun i => q (i :: w)) (commutedSource A g q w) U := by
  revert hw
  induction w with
  | nil =>
    intro _
    simpa only [commutedSource, commutatorExpression, JetExpression.eval, add_zero] using heq
  | cons i w ih =>
    intro hw
    have hws : w.length + 1 ≤ s := by simpa only [List.length_cons] using hw
    exact commuted_divergence_equation A g q
      (hq.mono (by omega : w.length + 2 ≤ s + 2)) (hg.mono hws) w le_rfl i (ih (by omega))

theorem norm_weakJet_second_le (q : List (Fin n) → L2) {s : ℕ}
    (hq : IsWeakSchwartzJet q (s + 2))
    {K : Set V} (hK : IsCompact K) (hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {r ell B : ℝ}
    (hr : 0 < r) (hell : 0 < ell) (hB : 0 ≤ B)
    (hEll : ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (w : List (Fin n)) (hw : w.length ≤ s) (G : L2)
    (heq : DivergenceEquation A (fun i => q (i :: w)) G (cthickening (3 * r) K))
    (i j : Fin n) :
    ‖q (j :: i :: w)‖ ≤ (‖G‖ + (n : ℝ) * B * (∑ l, ‖q (l :: w)‖)) / ell := by
  obtain ⟨S, hSK, hSjet⟩ := exists_schwartz_approximation_of_finite_weak_jets
    q (s + 2) hK hqK (fun v hv l φ => by
      simpa only [inner_schwartz, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hq v hv l φ) hr
  have hSu : Tendsto (fun m => (orderedSchwartzDerivative w (S m)).toLp 2 volume)
      atTop (𝓝 (q w)) := hSjet w (by omega)
  have hSD (l : Fin n) : Tendsto (fun m =>
      (∂_{EuclideanSpace.single l (1 : ℝ)} (orderedSchwartzDerivative w (S m))).toLp 2 volume)
      atTop (𝓝 (q (l :: w))) := by
    exact hSjet (l :: w) (by simp only [List.length_cons]; omega)
  have hcompact (m : ℕ) : HasCompactSupport (orderedSchwartzDerivative w (S m)) :=
    (hSK m).1.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_orderedSchwartzDerivative_subset w (S m))
  have hsupp (m : ℕ) : tsupport (orderedSchwartzDerivative w (S m)) ⊆ cthickening r K :=
    (tsupport_orderedSchwartzDerivative_subset w (S m)).trans (hSK m).2
  have hthick : cthickening (r + r) (cthickening r K) ⊆ cthickening (3 * r) K := by
    simpa only [show r + r + r = 3 * r by ring] using
      cthickening_cthickening_subset (add_nonneg hr.le hr.le) hr.le K
  have hint (l : Fin n) : Integrable (q (l :: w) : V → ℝ) volume := by
    obtain ⟨K', hK', hqK'⟩ := hq.exists_ae_compact_support hK hqK w (by omega)
    exact (hq w (by omega) l).integrable_of_ae_compact_support hK' hqK'
  obtain ⟨W, hW⟩ := exists_secondDerivatives_of_approximation
    (fun m => orderedSchwartzDerivative w (S m)) (q w) (fun l => q (l :: w))
    hSu hSD A hcompact hsupp hr hell hB (fun x hx => hEll x (hthick hx)) hAB G hint
    (fun φ hφ hφK => heq φ hφ (hφK.trans hthick))
  have hactual := hq (i :: w) (by simp only [List.length_cons]; omega) j
  have he : q (j :: i :: w) = W i j := hactual.unique (hW i j).2
  simpa only [he] using (hW i j).1

theorem norm_weakJet_commuted_second_le (q g : List (Fin n) → L2) {s : ℕ}
    (hq : IsWeakSchwartzJet q (s + 2)) (hg : IsWeakSchwartzJet g s)
    {K : Set V} (hK : IsCompact K) (hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {r ell B : ℝ}
    (hr : 0 < r) (hell : 0 < ell) (hB : 0 ≤ B)
    (hEll : ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (heq : DivergenceEquation A (fun i => q [i]) (g []) (cthickening (3 * r) K))
    (w : List (Fin n)) (hw : w.length ≤ s) (i j : Fin n) :
    ‖q (j :: i :: w)‖ ≤
      (‖commutedSource A g q w‖ + (n : ℝ) * B * (∑ l, ‖q (l :: w)‖)) / ell :=
  norm_weakJet_second_le q hq hK hqK A hr hell hB hEll hAB w hw _
    (divergence_equation_commuted_of_jets A q g hq hg heq w hw) i j

end PoincareConjecture.M35.Uniqueness.Heat
