import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFaces
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalHalfBlocks

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem isFinitePLBallPair_original_vertex_coordinate_sector
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {C : Set X}
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (v : E) (hvK : v ∈ K.vertices) (hvC : (g v : X) ∈ interior C)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z)))
    (hvzero : ∀ i : Fin 2, B (g v) i.castSucc = 0) (signs : Fin 2 → Bool) :
    let V := K.barycentricDualBlock {v}
    let cuts := {z | ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0}
    IsFinitePLBallPair V3 (V.space ∩ cuts)
      {z | z ∈ V.space ∧ z ∈ cuts ∧
        (z ∈ (V.link v).space ∨ ∃ i : Fin 2, B (g z) i.castSucc = 0)} := by
  classical
  let V := K.barycentricDualBlock {v}
  let J := K.barycentricSubdivision
  have hJs : J.space = K.space := K.barycentricSubdivision_isSubdivision.space_eq
  let H' : C ≃ₜ J.space := H.trans (Homeomorph.setCongr hJs.symm)
  have hg' (z : J.space) : (g z : X) = (H'.symm z : X) := hg ⟨z, hJs.subset z.property⟩
  have hvJ : v ∈ J.vertices := K.barycentricSubdivision_isSubdivision.vertices_subset hvK
  have hVeq : V = J.closedStar v := K.barycentricDualBlock_singleton_eq_closedStar hvK
  have hcontain : ∀ s ∈ V.faces, ∃ t ∈ (K.closedStar v).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) :=
    fun _ hs => K.exists_original_star_face_of_vertex_dual_face hvK hs
  have hVB : MapsTo (fun z => (g z : X)) V.space B.source := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := mem_space_iff.mp hz
    obtain ⟨t, ht, hst⟩ := hcontain s hs
    exact hsource ((K.closedStar v).convexHull_subset_space ht (hst hzs))
  have hvV : v ∈ V.vertices := by
    rw [hVeq]
    change {v} ∈ J.faces ∧ insert v {v} ∈ J.faces
    exact ⟨hvJ, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self v)]
      using (show {v} ∈ J.faces from hvJ)⟩
  have hVself : V.closedStar v = V := by
    rw [hVeq]
    ext s
    change ((s ∈ J.faces ∧ insert v s ∈ J.faces) ∧
      insert v s ∈ J.faces ∧ insert v (insert v s) ∈ J.faces) ↔
      s ∈ J.faces ∧ insert v s ∈ J.faces
    simp only [Finset.insert_idem, and_self, and_assoc]
  have hnb := J.exists_original_open_neighborhood_inside_closedStar
    K.barycentricSubdivision_finite H' g hg' hvJ hvC B (hVeq ▸ hVB)
  rw [← hVeq] at hnb
  obtain ⟨hinj, _, hint⟩ := hnb
  let f : E → V3 := fun z => B (g z) - B (g v)
  let shift : V3 →ᴬ[ℝ] V3 :=
    ContinuousAffineMap.id ℝ V3 - ContinuousAffineMap.const ℝ V3 (B (g v))
  have hf : V.AffineOnFaces f := (hface.of_face_containment hcontain).postcomp shift
  have hfi : InjOn f V.space := by
    intro x hx y hy hxy
    exact hinj hx hy (sub_left_inj.mp hxy)
  have hfp : f v = 0 := sub_self _
  have hfint : (0 : V3) ∈ interior (f '' V.space) := by
    have himage : f '' V.space = (Homeomorph.subRight (B (g v))) ''
        ((fun z => B (g z)) '' V.space) := by rw [image_image]; rfl
    rw [himage, ← Homeomorph.image_interior]
    exact ⟨B (g v), hint, sub_self _⟩
  have hcoord (z : E) (i : Fin 2) : f z i.castSucc = B (g z) i.castSucc := by
    simp only [f, Pi.sub_apply, hvzero i, sub_zero]
  let cuts : Fin 2 → V3 →ₗ[ℝ] ℝ := fun i =>
    if signs i then LinearMap.proj i.castSucc else -(LinearMap.proj i.castSucc)
  have hpositive : ∃ w : V3, ∀ i, 0 < cuts i w := by
    refine ⟨![if signs 0 then 1 else -1, if signs 1 then 1 else -1, 0], ?_⟩
    intro i
    fin_cases i
    · cases hs : signs 0 <;> norm_num [cuts, hs]
    · cases hs : signs 1 <;> norm_num [cuts, hs]
  have hcutmem (z : E) : (∀ i, 0 ≤ cuts i (f z)) ↔ ∀ i : Fin 2,
      if signs i then 0 ≤ B (g z) i.castSucc else B (g z) i.castSucc ≤ 0 := by
    apply forall_congr'
    intro i
    cases hi : signs i <;> simp only [cuts, hi, Bool.false_eq_true, ↓reduceIte,
      LinearMap.neg_apply, LinearMap.proj_apply, hcoord, neg_nonneg]
  have hcutzero (z : E) : (∃ i, cuts i (f z) = 0) ↔
      ∃ i : Fin 2, B (g z) i.castSucc = 0 := by
    apply exists_congr
    intro i
    cases hi : signs i <;> simp only [cuts, hi, Bool.false_eq_true, ↓reduceIte,
      LinearMap.neg_apply, LinearMap.proj_apply, hcoord, neg_eq_zero]
  have hball := hf.isFinitePLBallPair_conical_halfspaces (K.barycentricDualBlock_finite {v})
    hfi hvV hVself hfp hfint (ContinuousLinearEquiv.refl ℝ V3) cuts hpositive
  simpa only [hcutmem, hcutzero, mem_setOf_eq] using hball

end PoincareConjecture.M76.Dehn
