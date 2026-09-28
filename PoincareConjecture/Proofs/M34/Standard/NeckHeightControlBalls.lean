import PoincareConjecture.Proofs.M34.Mathlib.FirstExitOpen
import PoincareConjecture.Proofs.M34.Standard.MetricComparisonCompleteness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]



theorem closure_ball_subset_ball_of_lt
    (g : RiemannianMetric n M) (o : M) {r s : ℝ} (hs : 0 < s) (hrs : r < s) :
    closure (g.ball o r) ⊆ g.ball o s := by
  let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
  have hcl : closure (g.ball o r) ⊆ {x | g.edist o x ≤ ENNReal.ofReal r} := by
    apply closure_minimal
    · intro x hx
      exact (show g.edist o x < ENNReal.ofReal r from hx).le
    · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  intro x hx
  exact (hcl hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs).mpr hrs)





theorem closure_normalized_ball_subset_of_collar
    (g : RiemannianMetric n M) {Y V : Set M} (hY : IsClosed Y) (hYV : Y ⊆ V)
    {o : M} (ho : o ∈ Y) {R : M → ℝ} {mu L r : ℝ}
    (hmu : 0 < mu) (hL : 0 < L) (hgap : 1 < mu * L ^ 2)
    (hboundary : ∀ x ∈ frontier Y, mu ≤ R x)
    (hbarrier : ∀ s : ℝ, s < L → g.ball o s ⊆ V)
    (hr : 0 < r) (hbounded : BddAbove (R '' g.ball o r))
    (hnormalized : sSup (R '' g.ball o r) = r⁻¹ ^ 2) :
    closure (g.ball o r) ⊆ V := by
  by_cases hcore : g.ball o r ⊆ Y
  · exact (closure_minimal hcore hY).trans hYV
  obtain ⟨z, hz, hzY⟩ := Set.not_subset.mp hcore
  obtain ⟨γ, hγ0, hγ1, hγ, _, hγball⟩ := g.exists_short_path_in_ball o z hz
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  obtain ⟨w, hw, hwfront⟩ := hconn.exists_mem_frontier_of_mem_not_mem hY
    (mem_image_of_mem γ (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
    (hγ0.symm ▸ ho)
    (mem_image_of_mem γ (show (1 : ℝ) ∈ Icc 0 1 by norm_num))
    (hγ1.symm ▸ hzY)
  have hwball : w ∈ g.ball o r := by
    obtain ⟨t, ht, rfl⟩ := hw
    exact hγball ht
  have hmur : mu ≤ r⁻¹ ^ 2 := (hboundary w hwfront).trans
    ((le_csSup hbounded (mem_image_of_mem R hwball)).trans_eq hnormalized)
  have hproduct : mu * r ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hmur (sq_nonneg r)
    have heq : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp
    exact h.trans_eq heq
  have hrL : r < L := by
    by_contra hnot
    have hsq : L ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hL.le hr.le).mpr (le_of_not_gt hnot)
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hsq hmu.le).trans hproduct)) hgap
  obtain ⟨s, hrs, hsL⟩ := exists_between hrL
  exact (g.closure_ball_subset_ball_of_lt o (hr.trans hrs) hrs).trans (hbarrier s hsL)

end PoincareConjecture.RiemannianMetric
