import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.IntervalGerms
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalContactLineCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalGerm
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_two_segment_germs_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (sS : ChartwisePLSphere e S)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hyQ : y ∈ Q.source) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source)) ∩ U,
        x ≠ Q y → ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  exact h.exists_surface_contact_two_segment_germs_in_chart sS.chart_source_cover hgi hSV hpq hwp
    hwq ht hy Q hQ hyQ

theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_two_segment_germs_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (sS : ChartwisePLSphere e S)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E))) ∩ U,
        x ≠ Q y → ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  exact h.exists_surface_contact_two_segment_germs_of_affine_chart sS.chart_source_cover hgi hSV
    hpq hwp hwq ht hy Q hQ A hmap hA

theorem HasOriginalEdgeCofaceCharts.exists_triangle_interior_two_segment_germs_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (sS : ChartwisePLSphere e S)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
          intrinsicInterior ℝ (convexHull ℝ (A '' ({w, p, q} : Set E)))) ∩ U,
        ∃ u v : V3, u ≠ x ∧ v ≠ x ∧ segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  exact h.exists_surface_interior_two_segment_germs_of_affine_chart sS.chart_source_cover hgi hSV
    hpq hwp hwq ht hy Q hQ A hmap hA

end PoincareConjecture.M76
