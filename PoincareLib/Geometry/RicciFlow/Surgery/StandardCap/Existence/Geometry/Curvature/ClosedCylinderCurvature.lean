import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.FlowCurvatureContinuity

/-!
# Closing a half-open curvature window

Within-domain continuity extends the actual curvature norm bound to
the lower endpoint. No extension of the flow past that endpoint is used.
Source: Morgan-Tian Proposition 12.13, pp. 304-306, applying Theorem 8.1.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- A full curvature bound on a half-open time cylinder holds on its
closure whenever that closure remains inside the actual flow domain
(Proposition 12.13, pp. 304-306). -/
theorem closed_cylinder_curvature_bound {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {a b K : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (U : Set M)
    (hbound : ∀ s ∈ Ioc a b, ∀ q ∈ U, |(F.connection s).curvatureTensorNorm q| ≤ K) :
    ∀ s ∈ Icc a b, ∀ q ∈ U, (F.connection s).curvatureTensorNorm q ≤ K := by
  intro s hs q hq
  have hc : ContinuousOn (fun t => (F.connection t).curvatureTensorNorm q) (Icc a b) := by
    have h := (F.continuousOn_curvatureDerivativeNorm 0).comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨hJ ht, mem_univ q⟩)
    simpa only [Function.comp_def, id_eq, LeviCivitaData.curvatureDerivativeNorm_zero] using h
  have hclosure : closure (Ioc a b) = Icc a b := closure_Ioc (ne_of_lt hab)
  apply le_on_closure (fun t ht => (le_abs_self _).trans (hbound t ht q hq))
    (by rwa [hclosure]) continuousOn_const
  rwa [hclosure]

end PoincareMT.M34
