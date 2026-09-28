import PoincareConjecture.Proofs.M34.Standard.PathLengthComparison
import PoincareConjecture.Proofs.M34.Standard.MetricComparisonCompleteness
import PoincareConjecture.Proofs.M34.Mathlib.FirstExitLevel
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

theorem mapsTo_ball_of_local_speed_bound
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    {η : ℝ → M} {γ : ℝ → N} {o : M} {R C : ℝ}
    (hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 η (Icc (0 : ℝ) 1))
    (hη0 : η 0 = o) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, g.edist o (η t) ≤ ENNReal.ofReal R →
      g.tangentNorm (η t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η t 1) ≤
        C * h.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 m) γ t 1))
    (hlen : ENNReal.ofReal C * h.pathELength γ 0 1 < ENNReal.ofReal R) :
    MapsTo η (Icc (0 : ℝ) 1) (g.ball o R) := by
  let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
  have hd : ContinuousOn (fun t => g.edist o (η t)) (Icc (0 : ℝ) 1) :=
    continuous_edist.comp_continuousOn (continuousOn_const.prodMk hη.continuousOn)
  intro t ht
  by_contra hnot
  have hge : ENNReal.ofReal R ≤ g.edist o (η t) := le_of_not_gt hnot
  have ha : g.edist o (η 0) ≤ ENNReal.ofReal R := by
    rw [hη0]
    change g.comparisonPseudoEMetric.edist o o ≤ _
    rw [g.comparisonPseudoEMetric.edist_self]
    exact bot_le
  obtain ⟨s, hs, hlevel, hbefore⟩ :=
    (hd.mono (Icc_subset_Icc_right ht.2)).exists_first_eq_of_le ht.1 ha hge
  have hlength : g.pathELength η 0 s ≤ ENNReal.ofReal C * h.pathELength γ 0 s := by
    apply g.pathELength_le_mul_of_speed_le h η γ 0 s hC
    intro u hu
    exact hbound u ⟨hu.1, hu.2.trans_le (hs.2.trans ht.2)⟩
      (hbefore u ⟨hu.1.le, hu.2⟩).le
  have hmono : h.pathELength γ 0 s ≤ h.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_mono le_rfl (hs.2.trans ht.2)
  have hdist := g.edist_le_pathELength_of_mem_Icc
    (hη.mono (Icc_subset_Icc_right (hs.2.trans ht.2))) ⟨hs.1, le_rfl⟩
  rw [hη0, hlevel] at hdist
  exact (not_lt_of_ge (hdist.trans (hlength.trans (mul_le_mul' le_rfl hmono)))) hlen

end PoincareConjecture.RiemannianMetric
