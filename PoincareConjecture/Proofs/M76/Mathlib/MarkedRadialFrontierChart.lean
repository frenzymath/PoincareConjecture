import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexFrontier
import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingPlane










set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_finitePL_radial_frontier_section_preserving_zero
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    (A : E →ₗ[ℝ] ℝ) (hA : K.RespectsAffineHyperplane A.toAffineMap)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C)
    {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ e : K.space ≃ₜ
        (frontier C ∩ (NormedSpace.normalize ⁻¹'
          (NormedSpace.normalize '' K.space)) : Set E),
      e.IsFinitePL ∧ ∀ x : K.space, A (e x : E) = 0 ↔ A (x : E) = 0 := by
  classical
  obtain ⟨D, hD, hDK, hmin⟩ := K.exists_finite_subdivision_min_affine hK
    (fun i => -(L i).toAffineMap)
  have hlin := hDK.linearIndependent_faces hlinK
  have hrad : InjOn (NormedSpace.normalize : E → E) D.space :=
    hradK.mono hDK.space_eq.subset
  have hDzero : (0 : E) ∉ D.space := by
    intro hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    exact (hlin s hs).zero_notMem_convexHull hzs
  let r : E → ℝ := fun x => (gauge C x)⁻¹
  have hfront (x : E) (hx : x ∈ D.space) :
      0 < r x ∧ r x • x ∈ frontier C :=
    hC.gauge_inv_smul_mem_frontier hcv hzero (fun he => hDzero (he ▸ hx))
  have hr (x : E) (hx : x ∈ D.vertices) : 0 < r x :=
    (hfront x (D.vertices_subset_space hx)).1
  let R := D.radialRescale hlin hrad r hr
  have hRsub : R.space ⊆ frontier C := by
    intro y hy
    obtain ⟨_, ⟨s, hs, rfl⟩, hys⟩ := mem_space_iff.mp hy
    rw [Finset.coe_image] at hys
    obtain ⟨i, hi⟩ := hmin s hs
    have hvertices (v : E) (hv : v ∈ s) : L i (r v • v) = 1 := by
      apply linear_maximum_eq_one_of_radial_frontier L hL
        (hr v (D.face_subset_vertices hs hv))
      · intro j
        have h := hi v (subset_convexHull ℝ _ hv) j
        change -L i v ≤ -L j v at h
        exact neg_le_neg_iff.mp h
      · rw [← hrep]
        exact (hfront v (D.subset_space hs hv)).2
    have hyC : y ∈ C := convexHull_min (by
      rintro _ ⟨v, hv, rfl⟩
      exact hC.isClosed.frontier_subset (hfront v (D.subset_space hs hv)).2) hcv hys
    have hyi : L i y = 1 := (L i).eqOn_const_convexHull (by
      rintro _ ⟨v, hv, rfl⟩
      exact hvertices v hv) y hys
    rw [hrep, frontier_finite_linear_unit_halfspaces L hL]
    exact ⟨by simpa only [hrep, mem_ofPred_eq] using hyC, i, hyi⟩
  have hdirections : NormedSpace.normalize '' R.space =
      NormedSpace.normalize '' K.space := by
    rw [D.normalize_image_radialRescale_space hlin hrad r hr, hDK.space_eq]
  have hRs : R.space = (frontier C ∩ (NormedSpace.normalize ⁻¹'
      (NormedSpace.normalize '' K.space)) : Set E) := by
    apply Subset.antisymm
    · exact fun y hy => ⟨hRsub hy, hdirections ▸ mem_image_of_mem _ hy⟩
    · rintro y ⟨hyC, hydir⟩
      obtain ⟨z, hz, hzy⟩ := hdirections.symm ▸ hydir
      exact (hcv.injOn_normalize_frontier hzero (hRsub hz) hyC hzy) ▸ hz
  obtain ⟨f, _, e, hf, _, hfv, hef, _⟩ :=
    D.exists_radialRescale_homeomorph hD hlin hrad r hr
  have he : e.IsFinitePL := ⟨f, ⟨D, hD, rfl, hf⟩, hef⟩
  refine ⟨(Homeomorph.setCongr hDK.space_eq.symm).trans
    (e.trans (Homeomorph.setCongr hRs)), he.setCongr hDK.space_eq hRs, ?_⟩
  intro x
  change A (e ⟨x, hDK.space_eq.symm.subset x.property⟩ : E) = 0 ↔ A (x : E) = 0
  rw [hef]
  exact hf.linear_zero_iff_of_positive_vertex_rescaling r hr hfv A
    (hDK.respectsAffineHyperplane hA) x (hDK.space_eq.symm.subset x.property)



theorem exists_finitePL_link_convex_frontier_chart_preserving_zero
    [DecidableEq E] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : E →ₗ[ℝ] ℝ) (hA : (K.link 0).RespectsAffineHyperplane A.toAffineMap)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hdisj : Disjoint C (K.link 0).space)
    {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ e : (K.link 0).space ≃ₜ ((K.closedStar 0).space ∩ frontier C : Set E),
      e.IsFinitePL ∧ ∀ x : (K.link 0).space, A (e x : E) = 0 ↔ A (x : E) = 0 := by
  obtain ⟨e, he, heA⟩ := (K.link 0).exists_finitePL_radial_frontier_section_preserving_zero
    (finite_link_faces hK 0) (fun _ hs => linearIndependent_of_mem_link_zero hs)
    K.injOn_normalize_link A hA hC hcv hzero L hL hrep
  have heq := K.radial_frontier_section_eq_closedStar_inter hC.isClosed hcv hzero hdisj
  exact ⟨e.trans (Homeomorph.setCongr heq), he.setCongr rfl heq, heA⟩

end Geometry.SimplicialComplex
