import PoincareConjecture.Proofs.M35.Uniqueness.Heat.EquivalentTimeRegularity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {W V H : Type*} {m : ℕ}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem contDiffAt_finite_equivalent_weak_value
    (I : V →L[ℝ] H) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] V)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    {T B M q C : ℝ} (hT : 0 < T) (hTB : 2 * T ≤ B)
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hC : 0 ≤ C) (he : ‖e.toContinuousLinearMap‖ ≤ M)
    (P : ℝ → V →L[ℝ] V) (hP : ContDiffOn ℝ ∞ P (Icc 0 B))
    (hPb : ∀ t ∈ Icc 0 T, ‖P 0 - P t‖ ≤ q)
    (L : ℝ → PiLp 2 (fun _ : Fin m => V) →L[ℝ] PiLp 2 (fun _ : Fin m => H))
    (hL : ContDiffOn ℝ ∞ L (Icc 0 B)) (hLb : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C)
    (hbase : ∀ w u : W, inner ℝ w u =
      inner ℝ (I (e w)) (I (e u)) + inner ℝ (e w) (P 0 (e u)))
    (hsmall : (T + 1) * (M * (q * M)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1)
    {v : ℝ → PiLp 2 (fun _ : Fin m => V)} (hv : MemLp v 2 (timeMeasure B))
    {U : ℝ → PiLp 2 (fun _ : Fin m => H)} (hUc : ContinuousOn U (Icc 0 B))
    (hgraph : ∀ᵐ t ∂timeMeasure B, finiteHilbertMap I (v t) = U t)
    (heq : ∀ t ∈ Icc 0 B, ∀ w : PiLp 2 (fun _ : Fin m => V),
      inner ℝ (finiteHilbertMap I w) (U t) = inner ℝ (finiteHilbertMap I w) (U 0) +
        ∫ s in (0 : ℝ)..t, inner ℝ (finiteHilbertMap I w) (L s (v s)) -
          ∑ i, inner ℝ (w i) (P s (v s i)))
    {t : ℝ} (ht : t ∈ Ioc 0 T) : ContDiffAt ℝ ∞ U t := by
  let IV := finiteHilbertMap (m := m) I
  let E := finiteHilbertEquiv (m := m) e
  let PV : ℝ → PiLp 2 (fun _ : Fin m => V) →L[ℝ] PiLp 2 (fun _ : Fin m => V) :=
    fun s => finiteHilbertMapOperator (P s)
  have hIn : ‖IV.comp E.toContinuousLinearMap‖ ≤ 1 := by
    change ‖(finiteHilbertMap I).comp (finiteHilbertMap e.toContinuousLinearMap)‖ ≤ 1
    rw [← finiteHilbertMap_comp]
    exact (norm_finiteHilbertMap_le _).trans hJn
  have hEn : ‖E.toContinuousLinearMap‖ ≤ M :=
    (norm_finiteHilbertMap_le e.toContinuousLinearMap).trans he
  have hPV : ContDiffOn ℝ ∞ PV (Icc 0 B) := by
    simpa only [PV, Function.comp_def] using
      (finiteHilbertMapOperator (E := V) (F := V) (m := m)).contDiff.comp_contDiffOn hP
  have hPbV : ∀ s ∈ Icc 0 T, ‖PV 0 - PV s‖ ≤ q := by
    intro s hs
    change ‖finiteHilbertMapOperator (P 0) - finiteHilbertMapOperator (P s)‖ ≤ q
    rw [← map_sub]
    exact (norm_finiteHilbertMap_le _).trans (hPb s hs)
  have hBV (w u : PiLp 2 (fun _ : Fin m => W)) :
      inner ℝ w u = inner ℝ (IV (E w)) (IV (E u)) + inner ℝ (E w) (PV 0 (E u)) := by
    simp only [PiLp.inner_apply, IV, E, PV, finiteHilbertMapOperator_apply,
      finiteHilbertMap_apply, finiteHilbertEquiv_apply]
    simp_rw [hbase]
    exact Finset.sum_add_distrib
  apply contDiffAt_equivalent_weak_value IV
    (finiteHilbertMap_compact _ hIc) (finiteHilbertMap_denseRange _ hId)
    (finiteHilbertMap_injective _ hIi) E hIn hT hTB hM hq hC hEn
    PV hPV hPbV L hL hLb hBV hsmall hv hUc hgraph _ ht
  simpa only [IV, PV, finiteHilbertMapOperator_apply, PiLp.inner_apply,
    finiteHilbertMap_apply] using heq

end PoincareConjecture.M35.Uniqueness.Heat
