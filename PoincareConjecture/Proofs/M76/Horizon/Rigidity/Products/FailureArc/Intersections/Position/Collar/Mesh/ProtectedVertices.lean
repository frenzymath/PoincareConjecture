import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.Vertices
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.Restriction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_vertex_cleanup
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R U P : Set X}
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (V : Finset X) (hU : IsOpen U) (hP : IsClosed P)
    (hVU : (V : Set X) ⊆ U ∪ P) (hprotected : Disjoint S ((V : Set X) ∩ P))
    (hcharts : ∀ p ∈ V, p ∉ P → p ∈ S →
      (p ∈ interior R ∧ Nonempty (OriginalSurfacePairChart e S T p false)) ∨
      ∃ C : OriginalSurfacePairChart e S T p true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) :
    ∃ (F : X ≃ₜ X) (A : Set X),
      IsCompact A ∧ A ⊆ U ∧ Disjoint A P ∧ EqOn F id Aᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F ⁻¹' T = T ∧ F ⁻¹' R = R ∧ Disjoint (F '' S) (V : Set X) := by
  classical
  let W := V.filter (fun p => p ∉ P)
  have hWU : (W : Set X) ⊆ U ∩ Pᶜ := by
    intro p hp
    obtain ⟨hpV, hpP⟩ := Finset.mem_filter.mp hp
    exact ⟨(hVU hpV).resolve_right hpP, hpP⟩
  have hmodels : ∀ p ∈ W, p ∈ S →
      ∃ (b : Bool) (C : OriginalSurfacePairChart e S T p b) (B : Set (ℝ × ℝ)),
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ B := by
    intro p hp hpS
    obtain ⟨hpV, hpP⟩ := Finset.mem_filter.mp hp
    rcases hcharts p hpV hpP hpS with ⟨hpR, ⟨C⟩⟩ | ⟨C, hC⟩
    · obtain ⟨D, B, hD⟩ := C.exists_interior_region_model hpR
      exact ⟨false, D, B, hD⟩
    · exact ⟨true, C, {v | 0 ≤ v.2}, hC⟩
  obtain ⟨F, A, hA, hAU, hFoff, hFPL, hFinv, hFT, hFR, hFW⟩ :=
    exists_pair_chart_vertex_avoiding_motion hcover he W
      (hU.inter hP.isOpen_compl) hWU hmodels
  have hAP : Disjoint A P := disjoint_left.mpr (fun _ hx hp => (hAU hx).2 hp)
  refine ⟨F, A, hA, hAU.trans inter_subset_left, hAP, hFoff, hFPL, hFinv,
    hFT, hFR, disjoint_left.mpr ?_⟩
  intro p hpS hpV
  by_cases hpP : p ∈ P
  · have hpA : p ∉ A := fun hp => disjoint_left.mp hAP hp hpP
    have hpold : p ∈ S := by
      obtain ⟨q, hq, hqp⟩ := hpS
      exact F.injective (hqp.trans (hFoff hpA).symm) ▸ hq
    exact disjoint_left.mp hprotected hpold ⟨hpV, hpP⟩
  · exact disjoint_left.mp hFW hpS (Finset.mem_filter.mpr ⟨hpV, hpP⟩)

theorem protected_contacts_retained_by_vertex_cleanup
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S P A : Set X}
    {K : SimplicialComplex ℝ D} {g : D → X} {a : Finset D}
    (F : X ≃ₜ X) (hA : IsCompact A) (hAP : Disjoint A P)
    (hFoff : EqOn F id Aᶜ) (hedge : g '' convexHull ℝ (a : Set D) ⊆ P)
    (hfinite : (S ∩ (g '' convexHull ℝ (a : Set D))).Finite)
    (hcharts : HasOriginalEdgeCofaceCharts e S K g a) :
    (F '' S ∩ (g '' convexHull ℝ (a : Set D))).Finite ∧
      HasOriginalEdgeCofaceCharts e (F '' S) K g a := by
  have hAE : Disjoint A (g '' convexHull ℝ (a : Set D)) := hAP.mono_right hedge
  refine ⟨hfinite.subset ?_, hcharts.image_of_disjoint_support F hA.isClosed hAE hFoff⟩
  intro p hp
  have hpA : p ∉ A := fun h => disjoint_left.mp hAE h hp.2
  obtain ⟨q, hq, hqp⟩ := hp.1
  exact ⟨F.injective (hqp.trans (hFoff hpA).symm) ▸ hq, hp.2⟩

end PoincareConjecture.M76
