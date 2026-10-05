import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.PathLengthComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.MetricComparisonCompleteness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.FirstExitLevel
import PoincareLib.Geometry.Riemannian.Distance.CompactConfinement

/-!
# First-exit confinement from a local path-speed comparison

The speed estimate is required only while the path remains in the closed
comparison ball. A shorter comparison path excludes the first exit. All
distances and lengths are the actual selected metric values, including
infinite distances. Source: Morgan-Tian Theorem 12.29 and Claim 12.30,
pp. 324-325; reverse-ball-localization.md.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RiemannianMetric

/-- A local speed bound on a closed ball confines the whole path when
the scaled comparison length is strictly smaller than its radius.
No completeness, connectedness or endpoint differentiability is used
(Theorem 12.29, pp. 324-325). -/
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

end PoincareMT.RiemannianMetric
