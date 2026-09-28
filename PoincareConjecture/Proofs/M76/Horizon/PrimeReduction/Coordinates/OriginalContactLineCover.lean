import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.LineCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.OriginalContactGraph
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSphereChartCarrier
import PoincareConjecture.Proofs.M76.PrimeReduction.AffineContactFiniteness
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds

set_option autoImplicit false

open Set Geometry Module

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_line_cover_in_chart
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
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ A ∈ L, finrank ℝ A.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source)) ∩ U,
        ∃ A ∈ L, x ∈ A := by
  exact h.exists_surface_contact_line_cover_in_chart sS.chart_source_cover hgi hSV hpq hwp hwq ht
    hy Q hQ hyQ

theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_line_cover_of_affine_chart
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
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ B ∈ L, finrank ℝ B.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
        convexHull ℝ (A '' ({w, p, q} : Set E))) ∩ U, ∃ B ∈ L, x ∈ B := by
  exact h.exists_surface_contact_line_cover_of_affine_chart sS.chart_source_cover hgi hSV hpq hwp
    hwq ht hy Q hQ A hmap hA

end PoincareConjecture.M76
