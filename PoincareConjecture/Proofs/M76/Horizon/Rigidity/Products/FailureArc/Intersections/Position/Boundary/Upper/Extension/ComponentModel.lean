import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.BoundaryLift
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_finitePL_component_in_collar_base
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {K : Set E} {S B : Set X} (hSB : S ⊆ B)
    (hS : IsClopen ((Subtype.val : B → X) ⁻¹' S))
    (HB : K ≃ₜ B) {a : ℝ} (ha : 0 ≤ a)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (K ×ˢ Icc (0 : ℝ) a))
    (hi : InjOn c (K ×ˢ Icc (0 : ℝ) a))
    (hbase : ∀ x : K, c (x, 0) = HB x)
    (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite)
    (F : Z → X) (hF : PolyhedralPLInCharts e F A.space)
    (H : A.space ≃ₜ S) (hFval : ∀ x : A.space, F x = (H x : X)) :
    ∃ (L : SimplicialComplex ℝ E) (Q : A.space ≃ₜ L.space),
      L.faces.Finite ∧ L.space ⊆ K ∧ Q.IsFinitePL ∧
      (∀ x : A.space, c (Q x, 0) = (H x : X)) ∧
      IsClopen ((Subtype.val : K → E) ⁻¹' L.space) ∧
      ∀ x : K, (x : E) ∈ L.space ↔ (HB x : X) ∈ S := by
  have hFB : MapsTo F A.space B := by
    intro x hx
    rw [hFval ⟨x, hx⟩]
    exact hSB (H ⟨x, hx⟩).property
  obtain ⟨q, hq, hqK, hqval⟩ := exists_original_collar_boundary_lift
    hcompat HB ha c hc hi hbase A hA F hF hFB
  have hFi : InjOn F A.space := by
    intro x hx y hy hxy
    have heq : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hFval ⟨x, hx⟩).symm.trans (hxy.trans (hFval ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.injective heq)
  have hqi : InjOn q A.space := by
    intro x hx y hy hxy
    apply hFi hx hy
    rw [← hqval x hx, ← hqval y hy, hxy]
  obtain ⟨Q, hQ, hQval⟩ := hq.exists_homeomorph_image hqi
  obtain ⟨L, hL, hLs⟩ := hq.exists_finite_triangulation_image
  let QL : A.space ≃ₜ L.space := Q.trans (Homeomorph.setCongr hLs.symm)
  have hQL (x : A.space) : (QL x : E) = q x := hQval x
  have hsub : L.space ⊆ K := by
    rw [hLs]
    exact image_subset_iff.mpr hqK
  have hmark (x : K) : (x : E) ∈ L.space ↔ (HB x : X) ∈ S := by
    constructor
    · intro hx
      obtain ⟨z, hz, hzx⟩ := hLs.subset hx
      have heq : (HB x : X) = H ⟨z, hz⟩ := by
        rw [← hbase x, ← hzx, hqval z hz, hFval ⟨z, hz⟩]
      exact heq.symm ▸ (H ⟨z, hz⟩).property
    · intro hx
      obtain ⟨z, hz⟩ := H.surjective ⟨HB x, hx⟩
      have hzval : F z = (HB x : X) := (hFval z).trans (congrArg Subtype.val hz)
      have hqx : q z = (x : E) := by
        exact congrArg Prod.fst (hi ⟨hqK z.property, le_rfl, ha⟩ ⟨x.property, le_rfl, ha⟩
          ((hqval z z.property).trans (hzval.trans (hbase x).symm)))
      exact hLs.symm.subset ⟨z, z.property, hqx⟩
  have hclopen : IsClopen ((Subtype.val : K → E) ⁻¹' L.space) := by
    have heq : ((Subtype.val : K → E) ⁻¹' L.space) =
        HB ⁻¹' ((Subtype.val : B → X) ⁻¹' S) := by
      ext x
      exact hmark x
    rw [heq]
    exact hS.preimage HB.continuous
  refine ⟨L, QL, hL, hsub, ⟨q, hq, hQL⟩, ?_, hclopen, hmark⟩
  intro x
  rw [hQL, hqval x x.property, hFval]

end PoincareConjecture.M76
