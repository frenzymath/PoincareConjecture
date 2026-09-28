import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineMinimum











set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_finitePL_convex_frontier_radial_data (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s t : Set E} (hs : IsCompact s) (ht : IsCompact t)
    (hscv : Convex ℝ s) (htcv : Convex ℝ t)
    (hs0 : (0 : E) ∈ interior s) (ht0 : (0 : E) ∈ interior t)
    (hspace : K.space = frontier s)
    {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : t = {x | ∀ i, L i x ≤ 1}) :
    ∃ D : SimplicialComplex ℝ E, D.faces.Finite ∧ D.IsSubdivision K ∧
      ∃ f : E → E, D.AffineOnFaces f ∧
        EqOn f (fun x => (gauge t x)⁻¹ • x) D.vertices ∧
        ∃ e : frontier s ≃ₜ frontier t, e.IsFinitePL ∧
          ∀ x : frontier s, (e x : E) = f x := by
  classical
  obtain ⟨D, hD, hDK, hmin⟩ := K.exists_finite_subdivision_min_affine hK
    (fun i => -(L i).toAffineMap)
  have hDs : D.space = frontier s := hDK.space_eq.trans hspace
  have hlin := D.linearIndependent_faces_of_space_subset_frontier hscv hs0 hDs.subset
  have hinj : InjOn (normalize : E → E) D.space :=
    hscv.injOn_normalize_frontier hs0 |>.mono hDs.subset
  let r : E → ℝ := fun x => (gauge t x)⁻¹
  have hrad (x : E) (hx : x ∈ D.space) : 0 < r x ∧ r x • x ∈ frontier t := by
    apply ht.gauge_inv_smul_mem_frontier htcv ht0
    intro he
    have hxf : x ∈ frontier s := hDs ▸ hx
    exact hxf.2 (he ▸ hs0)
  have hr (x : E) (hx : x ∈ D.vertices) : 0 < r x :=
    (hrad x (D.vertices_subset_space hx)).1
  let R := D.radialRescale hlin hinj r hr
  have hRsub : R.space ⊆ frontier t := by
    intro y hy
    obtain ⟨_, ⟨u, hu, rfl⟩, hyu⟩ := mem_space_iff.mp hy
    rw [Finset.coe_image] at hyu
    obtain ⟨i, hi⟩ := hmin u hu
    have hvertices (v : E) (hv : v ∈ u) : L i (r v • v) = 1 := by
      apply linear_maximum_eq_one_of_radial_frontier L hL
        (hr v (D.face_subset_vertices hu hv))
      · intro j
        have h := hi v (subset_convexHull ℝ _ hv) j
        change -L i v ≤ -L j v at h
        exact neg_le_neg_iff.mp h
      · rw [← hrep]
        exact (hrad v (D.subset_space hu hv)).2
    have hyT : y ∈ t := convexHull_min (by
      rintro _ ⟨v, hv, rfl⟩
      exact ht.isClosed.frontier_subset (hrad v (D.subset_space hu hv)).2) htcv hyu
    have hyi : L i y = 1 := (L i).eqOn_const_convexHull (by
      rintro _ ⟨v, hv, rfl⟩
      exact hvertices v hv) y hyu
    rw [hrep, frontier_finite_linear_unit_halfspaces L hL]
    exact ⟨by simpa only [hrep, mem_ofPred_eq] using hyT, i, hyi⟩
  have hRs : R.space = frontier t := by
    apply Subset.antisymm hRsub
    intro y hy
    have hy0 : y ≠ 0 := fun he => hy.2 (he ▸ ht0)
    obtain ⟨x, hx, hxy⟩ := hs.exists_frontier_normalize_eq hscv hs0 hy0
    have hxD : x ∈ D.space := hDs.symm ▸ hx
    have hnorm : NormedSpace.normalize y ∈ NormedSpace.normalize '' R.space := by
      rw [D.normalize_image_radialRescale_space hlin hinj r hr]
      exact ⟨x, hxD, hxy⟩
    obtain ⟨z, hz, hzy⟩ := hnorm
    exact (htcv.injOn_normalize_frontier ht0 (hRsub hz) hy hzy) ▸ hz
  obtain ⟨f, _, e, hf, _, hfv, hef, _⟩ :=
    D.exists_radialRescale_homeomorph hD hlin hinj r hr
  have he : e.IsFinitePL := ⟨f, ⟨D, hD, rfl, hf⟩, hef⟩
  refine ⟨D, hD, hDK, f, hf, hfv,
    (Homeomorph.setCongr hDs.symm).trans (e.trans (Homeomorph.setCongr hRs)),
    he.setCongr hDs hRs, ?_⟩
  intro x
  exact hef ⟨x, hDs.symm ▸ x.property⟩

end Geometry.SimplicialComplex
