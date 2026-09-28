import PoincareConjecture.Proofs.M76.Mathlib.BasisFaceSpanProjection
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialLinearImage
import PoincareConjecture.Proofs.M76.Mathlib.UniformSecantProjection

set_option autoImplicit false

open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isRadialEmbedding_of_injOn_basisCone (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (A.basisRadialEmbedding b).cone.space) :
    A.IsRadialEmbedding (fun i => Q (b i)) := by
  classical
  let v := A.basisRadialEmbedding b
  let K := v.complex
  have hsimplex : ∀ s ∈ A.faces,
      convexHull ℝ (insert 0 (b '' (s : Set ι))) ⊆ v.cone.space := by
    intro s hs
    rw [v.cone_space]
    exact subset_iUnion₂_of_subset s (mem_insert_of_mem _ hs) Subset.rfl
  have hbase : K.space ⊆ v.cone.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact SimplicialComplex.convexHull_subset_space
      (SimplicialComplex.le_coneAtZero v.complex_linearIndependent v.complex_injOn_normalize hs) hxs
  have hzero : (0 : E) ∈ v.cone.space :=
    SimplicialComplex.vertices_subset_space
      (SimplicialComplex.zero_mem_coneAtZero_vertices
        v.complex_linearIndependent v.complex_injOn_normalize)
  have hvertices : ∀ i, b i ∈ v.cone.space := by
    intro i
    apply hbase
    apply SimplicialComplex.vertices_subset_space
    rw [v.complex_vertices]
    exact mem_range_self i
  have hspan : ∀ t ∈ K.faces, InjOn Q (Submodule.span ℝ (t : Set E)) := by
    intro t ht
    rw [v.complex_faces] at ht
    obtain ⟨s, hs, hts⟩ := ht
    change (t : Set E) = b '' (s : Set ι) at hts
    rw [hts]
    exact b.injOn_span_of_injOn_simplex Q (hQ.mono (hsimplex s hs))
  let L := K.linearImage v.complex_linearIndependent Q hspan (hQ.mono hbase)
  have hfaces : L.faces = {t : Finset F |
      ∃ s ∈ A.faces, (t : Set F) = (fun i => Q (b i)) '' (s : Set ι)} := by
    rw [SimplicialComplex.linearImage_faces, v.complex_faces_image, Set.image_image]
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp only [Finset.coe_image, Set.image_image]; rfl⟩
    · rintro ⟨s, hs, he⟩
      refine ⟨s, hs, Finset.coe_injective ?_⟩
      simpa only [Finset.coe_image, Set.image_image] using
        (show (fun i => Q (v.val i)) '' (s : Set ι) = (t : Set F) from he.symm)
  refine ⟨fun i j he => b.injective (hQ (hvertices i) (hvertices j) he), L, hfaces,
    fun t ht => SimplicialComplex.linearIndependent_linearImage_face
      v.complex_linearIndependent Q hspan (hQ.mono hbase) ht, ?_⟩
  intro x hx y hy he
  rw [SimplicialComplex.linearImage_space] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨s', hs', hus⟩ := SimplicialComplex.mem_space_iff.mp hu
  obtain ⟨t', ht', hwt⟩ := SimplicialComplex.mem_space_iff.mp hw
  have hu0 : u ≠ 0 := fun he =>
    (v.complex_linearIndependent s' hs').zero_notMem_convexHull (he ▸ hus)
  have hw0 : w ≠ 0 := fun he =>
    (v.complex_linearIndependent t' ht').zero_notMem_convexHull (he ▸ hwt)
  have hQu : Q u ≠ 0 := fun he => hu0 (hQ (hbase hu) hzero (he.trans (map_zero Q).symm))
  have hQw : Q w ≠ 0 := fun he => hw0 (hQ (hbase hw) hzero (he.trans (map_zero Q).symm))
  rw [v.complex_faces] at hs' ht'
  obtain ⟨s, hs, hss'⟩ := hs'
  obtain ⟨t, ht, htt'⟩ := ht'
  have huc : u ∈ b.nonnegativeCone (s : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    apply ConvexCone.subset_hull
    exact convexHull_mono (subset_insert 0 (b '' (s : Set ι))) (hss' ▸ hus)
  have hwc : w ∈ b.nonnegativeCone (t : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    apply ConvexCone.subset_hull
    exact convexHull_mono (subset_insert 0 (b '' (t : Set ι))) (htt' ▸ hwt)
  have hru : 0 < ‖Q u‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hQu)
  have hrw : 0 < ‖Q w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hQw)
  have hdir : ‖Q u‖⁻¹ • u = ‖Q w‖⁻¹ • w := by
    apply sub_eq_zero.mp
    apply b.eq_zero_of_mem_secantCone_of_injOn (s := s) (t := t) Q
      (hQ.mono (union_subset (hsimplex s hs) (hsimplex t ht)))
    · exact (b.mem_secantCone_iff _ _ _).mpr
        ⟨_, (b.nonnegativeCone s).smul_mem hru huc,
          _, (b.nonnegativeCone t).smul_mem hrw hwc, rfl⟩
    · simpa only [map_sub, map_smul, NormedSpace.normalize] using sub_eq_zero.mpr he
  have hnorm : normalize u = normalize w := by
    calc
      normalize u = normalize (‖Q u‖⁻¹ • u) := (normalize_smul_of_pos hru u).symm
      _ = normalize (‖Q w‖⁻¹ • w) := congrArg NormedSpace.normalize hdir
      _ = normalize w := normalize_smul_of_pos hrw w
  exact congrArg Q (v.complex_injOn_normalize hu hw hnorm)

theorem isRadialEmbedding_iff_injOn_basisCone [FiniteDimensional ℝ F]
    (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔ InjOn Q (A.basisRadialEmbedding b).cone.space :=
  ⟨fun h => BasisRadialProjection.injOn_basisCone (⟨Q, h⟩ : A.BasisRadialProjection b F),
    A.isRadialEmbedding_of_injOn_basisCone b Q⟩

end AbstractSimplicialComplex
