import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization
import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.LinearIndependentFaceRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineMinimum
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets











set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_finitePL_radial_frontier_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C)
    {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ e : K.space ≃ₜ
        (frontier C ∩ (NormedSpace.normalize ⁻¹'
          (NormedSpace.normalize '' K.space)) : Set E), e.IsFinitePL := by
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
      have hym : NormedSpace.normalize y ∈ NormedSpace.normalize '' R.space :=
        hdirections.symm ▸ hydir
      obtain ⟨z, hz, hzy⟩ := hym
      exact (hcv.injOn_normalize_frontier hzero (hRsub hz) hyC hzy) ▸ hz
  obtain ⟨f, _, e, hf, _, _, hef, _⟩ :=
    D.exists_radialRescale_homeomorph hD hlin hrad r hr
  have he : e.IsFinitePL := ⟨f, ⟨D, hD, rfl, hf⟩, hef⟩
  exact ⟨(Homeomorph.setCongr hDK.space_eq.symm).trans
    (e.trans (Homeomorph.setCongr hRs)), he.setCongr hDK.space_eq hRs⟩

end Geometry.SimplicialComplex
