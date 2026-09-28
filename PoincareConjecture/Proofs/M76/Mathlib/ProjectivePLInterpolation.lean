import PoincareConjecture.Proofs.M76.Mathlib.HullImageLocalFiniteness
import PoincareConjecture.Proofs.M76.Mathlib.InfiniteSimplicialHomeomorph

set_option autoImplicit false

open Set Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_piecewiseAffine_interpolant (K : SimplicialComplex ℝ E)
    (e : OpenPartialHomeomorph E F) (hsource : K.space = e.source)
    (hK : ∀ x ∈ K.space, ∃ U ∈ 𝓝 x,
      {s : K.faces | (convexHull ℝ (s.val : Set E) ∩ U).Nonempty}.Finite)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ ((↑) : ↥(e '' (s : Set E)) → F))
    (hhull : ∀ s ∈ K.faces,
      e '' convexHull ℝ (s : Set E) = convexHull ℝ (e '' (s : Set E))) :
    ∃ p : OpenPartialHomeomorph E F,
      p.source = e.source ∧ p.target = e.target ∧ K.AffineOnFaces p ∧
      EqOn p e K.vertices ∧ LocallyPiecewiseAffineOn p p.source ∧
      LocallyPiecewiseAffineOn p.symm p.target := by
  classical
  let D := K.hullImage e (e.injOn.mono hsource.subset) hind hhull
  have hDspace : D.space = e.target := by
    rw [hullImage_space, hsource, e.image_source_eq_target]
  have hDlocal := K.local_faces_hullImage e hsource.subset hind hhull hK
  have hKopen : IsOpen K.space := hsource ▸ e.open_source
  have hDopen : IsOpen D.space := hDspace ▸ e.open_target
  have hv : ∀ s ∈ K.faces, ∃ t ∈ D.faces, e '' (s : Set E) ⊆ (t : Set F) := by
    intro s hs
    refine ⟨s.image e, ?_, ?_⟩
    · exact (K.hullImage_faces e (e.injOn.mono hsource.subset) hind hhull) ▸
        mem_image_of_mem _ hs
    · rw [Finset.coe_image]
  have hw : ∀ t ∈ D.faces, ∃ s ∈ K.faces, e.symm '' (t : Set F) ⊆ (s : Set E) := by
    intro t ht
    rw [hullImage_faces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s, hs, ?_⟩
    rw [Finset.coe_image]
    rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    rwa [e.left_inv (hsource.subset (K.subset_space hs hx))]
  have hleft : LeftInvOn e.symm e K.vertices :=
    fun _ hx => e.left_inv (hsource.subset (K.vertices_subset_space hx))
  have hright : RightInvOn e.symm e D.vertices :=
    fun _ hy => e.right_inv (hDspace.subset (D.vertices_subset_space hy))
  obtain ⟨f, g, q, hf, _, hfv, _, hfPL, hgPL, hq, hqi⟩ :=
    K.exists_homeomorph_of_local_vertex_maps D hKopen hDopen hK hDlocal
      e e.symm hv hw hleft hright
  have hfmap : MapsTo f K.space D.space := by
    intro x hx
    rw [← hq ⟨x, hx⟩]
    exact (q ⟨x, hx⟩).property
  have hgmap : MapsTo g D.space K.space := by
    intro y hy
    rw [← hqi ⟨y, hy⟩]
    exact (q.symm ⟨y, hy⟩).property
  have hgf : LeftInvOn g f K.space := by
    intro x hx
    have he := congrArg Subtype.val (q.symm_apply_apply ⟨x, hx⟩)
    simpa only [hqi, hq] using he
  have hfg : RightInvOn g f D.space := by
    intro y hy
    have he := congrArg Subtype.val (q.apply_symm_apply ⟨y, hy⟩)
    simpa only [hq, hqi] using he
  let p : OpenPartialHomeomorph E F :=
    { toFun := f
      invFun := g
      source := K.space
      target := D.space
      map_source' := fun _ hx => hfmap hx
      map_target' := fun _ hy => hgmap hy
      left_inv' := fun _ hx => hgf hx
      right_inv' := fun _ hy => hfg hy
      open_source := hKopen
      open_target := hDopen
      continuousOn_toFun := hfPL.continuousOn
      continuousOn_invFun := hgPL.continuousOn }
  exact ⟨p, hsource, hDspace, hf, hfv, hfPL, hgPL⟩

end Geometry.SimplicialComplex
