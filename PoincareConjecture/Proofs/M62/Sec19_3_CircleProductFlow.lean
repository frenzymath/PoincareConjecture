import PoincareConjecture.Proofs.M62.Sec19_3_CircleMetric
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductFamily
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductRicci










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem nonempty_circleProductData [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) (circumference : ℝ)
    (hp : 0 < circumference) : Nonempty (CircleProductData F circumference) := by
  classical
  obtain ⟨C⟩ := nonempty_circleGeometry hp
  obtain ⟨P⟩ := nonempty_circleProductCharts (n := n) (M := M) C
  let := P.chartedSpace
  choose G hG using fun t : ℝ => exists_circleProductMetric (F.metric t) C P
  let D : (t : ℝ) → LeviCivitaData (G t) :=
    fun t => Classical.choice (m01_exists_leviCivitaData (G t))
  let H : RicciFlow (n + 1) P.Point (Set.Icc a b) := {
    metric := G
    connection := D
    interval := F.interval
    nontrivial := F.nontrivial
    smooth := circleProductMetric_isSmoothFamilyOn F C P G hG
    equation := by
      intro t ht q V W
      have h := (F.equation t ht q.1 (P.split q V).1 (P.split q W).1).add_const
        (C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
      have hr := circleProduct_ricci (F.metric t) (F.connection t) C P (G t) (D t) (hG t)
        q V W
      simpa only [hG, hr] using h
  }
  exact ⟨⟨C, P, H, hG⟩⟩

end PoincareConjecture.M62
