import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.MetricConvergence
import PoincareLib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local diffeomorphisms on captured spatial limit charts

The retained source embedding is used only where the inverse limit chart
lands in its genuine exhaustion domain. Restricting to an open Euclidean
domain gives the actual local coordinate map used for backward flows.
Morgan--Tian Theorem 5.6 and Proposition 5.14, pp. 85-87 and 90-91;
M28 derivation 74.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.RegularPointedMetricConvergence

/-- Restricting the retained embedding to a captured inverse limit chart
gives a local diffeomorphism on the canonical domain. There is no assertion
about the total embedding outside its exhaustion (derivation 74). -/
theorem chart_embedding_localDiffeomorph
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (k : ℕ)
      (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U],
      U ⊆ (extChartAt (𝓡 n) q).target →
      (extChartAt (𝓡 n) q).symm '' U ⊆ G.exhaustion k →
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
        (fun x : U => G.embedding k ((extChartAt (𝓡 n) q).symm x.val)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro q k U hU _ htarget hcapture
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let d : PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier ∞ := {
    toPartialEquiv := (extChartAt (𝓡 n) q).symm
    open_source := isOpen_extChartAt_target q
    open_target := isOpen_extChartAt_source q
    contMDiffOn_toFun := contMDiffOn_extChartAt_symm q
    contMDiffOn_invFun := by
      change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) q)
        (extChartAt (𝓡 n) q).source
      simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := q)) }
  intro x
  have hval := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n) U hU ∞ x
  have hchart := d.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (htarget x.property)
  have hsource := G.embedding_smooth k
    ⟨(extChartAt (𝓡 n) q).symm x.val, hcapture ⟨x.val, x.property, rfl⟩⟩
  exact (hval.comp (𝓡 n) G.limitCarrier.carrier hchart).comp
    (𝓡 n) (M (G.subsequence k)) hsource

end PoincareMT.M28.RegularPointedMetricConvergence
