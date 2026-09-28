import PoincareConjecture.Proofs.M14.Sec6_2_ClosedJacobiODE










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)



noncomputable def closedCoordinateAdaptedOperator (C : Set ℝ)
    (q : ℝ → EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  -M08.closedChartConnection F T x C (s, q s) (derivWithin q C s) -
    (1 / 2 : ℝ) • ((M08.chartMetricDualInverse F T x (s, q s)).comp
      (M08.timeWithinFDeriv C (extChartAt (𝓡 n) x).target
        (M08.chartActionMetric F T x) (s, q s)))



theorem closedCoordinateAdaptedOperator_contDiffOn
    {C : Set ℝ} (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ J)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContDiffOn ℝ ∞ q C)
    (hmem : MapsTo q C (extChartAt (𝓡 n) x).target) :
    ContDiffOn ℝ ∞ (closedCoordinateAdaptedOperator F T x C q) C := by
  have hpoint := contDiffOn_id.prodMk hq
  have hmap : MapsTo (fun s => (s, q s)) C (C ×ˢ (extChartAt (𝓡 n) x).target) :=
    fun _ hs => ⟨hs, hmem hs⟩
  have hA := hq.derivWithin hC (m := ∞) (by simp)
  have hB := (M08.chartMetricDualInverse_contDiffOn F T x htime).comp hpoint hmap
  have hΓ := ((M08.closedChartConnection_contDiffOn F T x hC htime).comp hpoint hmap).clm_apply hA
  have hH := (M08.timeWithinFDeriv_contDiffOn hC (isOpen_extChartAt_target (I := 𝓡 n) x)
    (M08.chartActionMetric F T x) (M08.chartActionMetric_closed_contDiffOn F T x htime)).comp
    hpoint hmap
  exact hΓ.neg.sub ((contDiffOn_const (c := (1 / 2 : ℝ))).smul (hB.clm_comp hH))




theorem exists_closedCoordinateAdapted_solution
    {a b t₀ : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContDiffOn ℝ ∞ q (Icc a b))
    (hmem : MapsTo q (Icc a b) (extChartAt (𝓡 n) x).target)
    (ht₀ : t₀ ∈ Icc a b) (v₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ v : ℝ → EuclideanSpace ℝ (Fin n), v t₀ = v₀ ∧ ContDiffOn ℝ ∞ v (Icc a b) ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt v
        (closedCoordinateAdaptedOperator F T x (Icc a b) q s (v s)) (Icc a b) s := by
  have hL := closedCoordinateAdaptedOperator_contDiffOn F T x (uniqueDiffOn_Icc hab)
    htime hq hmem
  obtain ⟨v, hv₀, hvd⟩ := M08.exists_linear_interval_solution _ hL.continuousOn ht₀ v₀
  exact ⟨v, hv₀, M08.linear_interval_solution_contDiffOn _ hL hvd, hvd⟩




theorem closedCoordinateAdapted_solution_unique
    {a b t₀ : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} (hq : ContDiffOn ℝ ∞ q (Icc a b))
    (hmem : MapsTo q (Icc a b) (extChartAt (𝓡 n) x).target) (ht₀ : t₀ ∈ Icc a b)
    {f g : ℝ → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ s ∈ Icc a b, HasDerivWithinAt f
      (closedCoordinateAdaptedOperator F T x (Icc a b) q s (f s)) (Icc a b) s)
    (hg : ∀ s ∈ Icc a b, HasDerivWithinAt g
      (closedCoordinateAdaptedOperator F T x (Icc a b) q s (g s)) (Icc a b) s)
    (heq : f t₀ = g t₀) : EqOn f g (Icc a b) :=
  M08.linear_interval_solution_unique _
    (closedCoordinateAdaptedOperator_contDiffOn F T x (uniqueDiffOn_Icc hab)
      htime hq hmem).continuousOn ht₀ hf hg heq

end PoincareConjecture.M14
