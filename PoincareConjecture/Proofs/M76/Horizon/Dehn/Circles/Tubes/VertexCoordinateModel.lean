import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ConvexCoordinateSection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalVertexCoordinateSectors

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in


theorem exists_original_vertex_coordinate_model
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {C : Set X}
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (H : C ≃ₜ K.space) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (v : E) (hvK : v ∈ K.vertices) (hvC : (g v : X) ∈ interior C)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar v).space B.source)
    (hface : (K.closedStar v).AffineOnFaces (fun z => B (g z))) :
    let V := K.barycentricDualBlock {v}
    ∃ (C0 : Set V3) (L : (Fin 3 ⊕ Fin 3) → V3 →ₗ[ℝ] ℝ)
      (theta : V.space ≃ₜ C0),
      IsCompact C0 ∧ Convex ℝ C0 ∧ (0 : V3) ∈ interior C0 ∧
      (∀ j, L j ≠ 0) ∧ C0 = {x | ∀ j, L j x ≤ 1} ∧
      theta.IsFinitePL ∧ theta.symm.IsFinitePL ∧
      (∀ z : V.space, (z : E) ∈ (V.link v).space ↔ (theta z : V3) ∈ frontier C0) ∧
      ∀ j (z : V.space),
        ((theta z : V3) j = 0 ↔ (B (g z) - B (g v)) j = 0) ∧
        (0 ≤ (theta z : V3) j ↔ 0 ≤ (B (g z) - B (g v)) j) := by
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

  have hVfin : V.faces.Finite := K.barycentricDualBlock_finite {v}
  let I := hf.embeddedImage hfi
  have hI : I.faces.Finite := hf.embeddedImage_finite hfi hVfin
  have hIs : I.space = f '' V.space := hf.embeddedImage_space hfi
  have hIstar : (I.closedStar 0).space = f '' V.space := by
    simpa only [hfp, hVself] using hf.embeddedImage_closedStar_space hfi hvV
  have hIlink : (I.link 0).space = f '' (V.link v).space := by
    simpa only [hfp] using hf.embeddedImage_link_space hfi hvV
  have hzI : (0 : V3) ∈ I.vertices := by
    rw [hf.embeddedImage_vertices hfi]
    exact ⟨v, hvV, hfp⟩
  obtain ⟨C0, L, T, hC, hcv, hC0, hL, hrep, hT, hTlink, hcuts⟩ :=
    I.exists_finitePL_closedStar_chart_preserving_cut_family hI hzI
      (hIs.symm ▸ hfint) (ContinuousLinearEquiv.refl ℝ V3)
      (fun j : Fin 3 => LinearMap.proj j)
  let u : V.space ≃ₜ (I.closedStar 0).space :=
    (hf.homeomorphImage hVfin hfi).trans (Homeomorph.setCongr hIstar.symm)
  have hu : u.IsFinitePL := ⟨f, hf.finitePiecewiseAffineOn hVfin, fun _ => rfl⟩
  let theta : V.space ≃ₜ C0 := u.trans T
  have htheta : theta.IsFinitePL := hu.trans hT
  have hlinksub : (V.link v).space ⊆ V.space :=
    space_subset_of_le (show V.link v ≤ V from fun _ hs => hs.1)
  have hlink (z : V.space) : (z : E) ∈ (V.link v).space ↔ (theta z : V3) ∈ frontier C0 := by
    have hfz : f z ∈ (I.link 0).space ↔ (z : E) ∈ (V.link v).space := by
      rw [hIlink]
      exact ⟨fun ⟨w, hw, he⟩ => hfi (hlinksub hw) z.property he ▸ hw,
        fun hz => mem_image_of_mem f hz⟩
    exact hfz.symm.trans (hTlink (u z))
  have hmarks (j : Fin 3) (z : V.space) :
      ((theta z : V3) j = 0 ↔ f z j = 0) ∧
      (0 ≤ (theta z : V3) j ↔ 0 ≤ f z j) := hcuts j (u z)

  exact ⟨C0, L, theta, hC, hcv, hC0, hL, hrep, htheta, htheta.symm, hlink, hmarks⟩

end PoincareConjecture.M76.Dehn

