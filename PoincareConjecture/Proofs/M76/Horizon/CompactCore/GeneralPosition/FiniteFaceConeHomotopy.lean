import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ProtectedFaceCone
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaries
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.FiniteSubcomplexHomotopyGluing










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_finite_face_cone_homotopy
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
    [TopologicalSpace X] [Nonempty X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (hcv : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty)
    (R : SimplicialComplex ℝ E) (hR : R.faces.Finite)
    (L : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
    (hLR : ∀ s, L s ≤ R)
    (hLS : ∀ s, (L s).space = frontier (convexHull ℝ (s.val.val : Set E)))
    (B : {s : K.faces // s.val.card = 3} → OpenPartialHomeomorph X V3)
    (hcompat : ∀ s i, (e i).symm.trans (B s) ∈ piecewiseAffineGroupoid V3)
    (f b : E → X) (A : {s : K.faces // s.val.card = 3} → E →ᴬ[ℝ] V3)
    (hfsource : ∀ s, MapsTo f (convexHull ℝ (s.val.val : Set E)) (B s).source)
    (hfcoord : ∀ s, EqOn (B s ∘ f) (A s) (convexHull ℝ (s.val.val : Set E)))
    (hb : ∀ s, (L s).AffineOnFaces (B s ∘ b))
    (W : {s : K.faces // s.val.card = 3} → Set V3)
    (hWopen : ∀ s, IsOpen (W s)) (hWcv : ∀ s, Convex ℝ (W s))
    (hWtarget : ∀ s, W s ⊆ (B s).target) (hWY : ∀ s, MapsTo (B s).symm (W s) Y)
    (hfW : ∀ s, MapsTo (A s) (convexHull ℝ (s.val.val : Set E)) (W s))
    (D : C(I × R.space, X))
    (hDcontrol : ∀ s (t : I) (x : (L s).space),
      D (t, ⟨x, space_subset_of_le (hLR s) x.property⟩) ∈ (B s).source ∧
      B s (D (t, ⟨x, space_subset_of_le (hLR s) x.property⟩)) ∈ W s)
    (hD0 : ∀ x : R.space, D (0, x) = f x)
    (hD1 : ∀ x : R.space, D (1, x) = b x) :
    ∃ (C : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
      (T : SimplicialComplex ℝ E) (G : C(I × K.space, X)) (g : E → X),
      T.faces.Finite ∧ T.space = K.space ∧ T.faces = ⋃ s, (C s).faces ∧
      (∀ s, (C s).faces.Finite ∧ (C s).space = convexHull ℝ (s.val.val : Set E) ∧
        L s ≤ C s ∧ C s ≤ T ∧
        (C s).vertices = insert (s.val.val.centroid ℝ id) (L s).vertices ∧
        (∀ z ∈ (L s).faces, insert (s.val.val.centroid ℝ id) z ∈ (C s).faces) ∧
        (∀ z, z ∈ (C s).faces ↔ z.Nonempty ∧
          (z.erase (s.val.val.centroid ℝ id) = ∅ ∨
            z.erase (s.val.val.centroid ℝ id) ∈ (L s).faces)) ∧
        (C s).AffineOnFaces (B s ∘ g) ∧ g (s.val.val.centroid ℝ id) ∉ F ∧
        EqOn g b (frontier (convexHull ℝ (s.val.val : Set E))) ∧
        ∀ x ∈ (C s).space, g x ∈ (B s).source ∧ B s (g x) ∈ W s ∧ g x ∈ Y) ∧
      (∀ s (t : I) (x : (C s).space) (hx : (x : E) ∈ K.space),
        G (t, ⟨x, hx⟩) ∈ (B s).source ∧ B s (G (t, ⟨x, hx⟩)) ∈ W s ∧
          G (t, ⟨x, hx⟩) ∈ Y) ∧
      (∀ s (t : I) (x : (L s).space) (hx : (x : E) ∈ K.space),
        G (t, ⟨x, hx⟩) = D (t, ⟨x, space_subset_of_le (hLR s) x.property⟩)) ∧
      (∀ x : K.space, G (0, x) = f x) ∧ (∀ x : K.space, G (1, x) = g x) ∧
      PolyhedralPLInCharts e g K.space := by
  classical
  let : Finite K.faces := hK.to_subtype
  let τ := {s : K.faces // s.val.card = 3}
  let S (s : τ) := convexHull ℝ (s.val.val : Set E)
  have hcompact (s : τ) : IsCompact (S s) := s.val.val.finite_toSet.isCompact_convexHull ℝ
  have hcenter (s : τ) : s.val.val.centroid ℝ id ∈ interior (S s) :=
    K.triangle_centroid_mem_interior hdim s.val.property s.property
  have hboundaryR (s : τ) : frontier (S s) ⊆ R.space :=
    (hLS s).symm.subset.trans (space_subset_of_le (hLR s))
  let Ds (s : τ) : C(I × frontier (S s), X) :=
    D.comp ⟨fun z => (z.1, ⟨z.2, hboundaryR s z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  have hDs (s : τ) (z : I × frontier (S s)) :
      Ds s z ∈ (B s).source ∧ B s (Ds s z) ∈ W s :=
    hDcontrol s z.1 ⟨z.2, (hLS s).symm.subset z.2.property⟩
  have hex (s : τ) := hN.exists_protected_face_cone hY hcut (B s) (hcompat s)
    (L s) (hR.subset (hLR s)) (hcompact s) (convex_convexHull ℝ _)
    (s.val.val.centroid ℝ id) (hcenter s) (hLS s) f b (A s) (hfsource s)
    (hfcoord s) (hb s) (hWopen s) (hWcv s) (hWtarget s) (hWY s) (hfW s)
    (Ds s) (fun z => (hDs s z).1) (fun z => (hDs s z).2)
    (fun u => hD0 ⟨u, hboundaryR s u.property⟩)
    (fun u => hD1 ⟨u, hboundaryR s u.property⟩)
  choose C g H hC hCS hLC hvertices hcones hfaces hcoord hPL hoff hboundary
    hgcontrol hHcontrol hray hH0 hH1 hHD using hex
  have hinter (s t : τ) (hne : s ≠ t) :
      (C s).space ∩ (C t).space ⊆ (L s).space ∩ (L t).space := by
    rw [hCS s, hCS t, hLS s, hLS t]
    exact K.distinct_triangle_inter_subset_frontiers s.val.property t.val.property
      s.property t.property (fun h => hne (Subtype.ext (Subtype.ext h)))
  have hcross : ∀ s t, ∀ u ∈ (C s).faces, ∀ v ∈ (C t).faces,
      convexHull ℝ (u : Set E) ∩ convexHull ℝ (v : Set E) ⊆
        convexHull ℝ ((u : Set E) ∩ v) := by
    intro s t u hu v hv
    by_cases hst : s = t
    · subst t
      exact (C s).inter_subset_convexHull hu hv
    · exact R.cross_inter_subset_of_shared_boundary (L s) (L t) (C s) (C t)
        (hLR s) (hLR t) (hLC s) (hLC t) (hinter s t hst) hu hv
  let T := iUnionOfCompatible C hcross
  have hT : T.faces.Finite := finite_faces_iUnionOfCompatible C hcross hC
  have hCT (s : τ) : C s ≤ T := le_iUnionOfCompatible C hcross s
  have hTS : T.space = K.space := by
    rw [space_iUnionOfCompatible C hcross]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact convexHull_subset_space s.val.property ((hCS s).subset hs)
    · intro x hx
      obtain ⟨s, hs, hcard, hxs⟩ := K.exists_full_face_of_mem_convex_space hK hcv hne hx
      have hc : s.card = 3 := by omega
      exact mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hc⟩, (hCS _).symm.subset hxs⟩
  let Hs (s : τ) : C(I × (C s).space, X) :=
    (H s).comp ⟨fun z => (z.1, ⟨z.2, (hCS s).subset z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  have hsame : ∀ s t (r : I) (x : E) (hs : x ∈ (C s).space) (ht : x ∈ (C t).space),
      Hs s (r, ⟨x, hs⟩) = Hs t (r, ⟨x, ht⟩) := by
    intro s t r x hs ht
    by_cases hst : s = t
    · subst t
      rfl
    · have hx := hinter s t hst ⟨hs, ht⟩
      have hxs := (hLS s).subset hx.1
      have hxt := (hLS t).subset hx.2
      exact (hHD s r ⟨x, hxs⟩).trans (hHD t r ⟨x, hxt⟩).symm
  obtain ⟨G, q, hG, hG1, hq, hqPL⟩ :=
    T.exists_polyhedralPL_homotopy_of_finite_subcomplex_cover e hN.cover hN.compatible hT
      C hCT (by rw [space_iUnionOfCompatible C hcross]) Hs hsame g
      (fun s => (hCS s).symm ▸ hPL s) (fun s x => hH1 s ⟨x, (hCS s).subset x.property⟩)
  let G' : C(I × K.space, X) :=
    G.comp ⟨fun z => (z.1, ⟨z.2, hTS.symm.subset z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  have hGlocal (s : τ) (r : I) (x : (C s).space) (hx : (x : E) ∈ K.space) :
      G' (r, ⟨x, hx⟩) = Hs s (r, x) := hG s r x
  refine ⟨C, T, G', q, hT, hTS, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    refine ⟨hC s, hCS s, hLC s, hCT s, hvertices s, hcones s, hfaces s, ?_, ?_, ?_, ?_⟩
    · exact (hcoord s).congr (fun x hx => congrArg (B s) (hq s hx).symm)
    · have hcC : s.val.val.centroid ℝ id ∈ (C s).space :=
        (hCS s).symm.subset (interior_subset (hcenter s))
      rw [hq s hcC]
      exact hoff s
    · intro x hx
      exact (hq s ((hCS s).symm.subset ((hcompact s).isClosed.frontier_subset hx))).trans
        (hboundary s hx)
    · intro x hx
      rw [hq s hx]
      exact hgcontrol s x ((hCS s).subset hx)
  · intro s r x hx
    rw [hGlocal s r x hx]
    exact hHcontrol s (r, ⟨x, (hCS s).subset x.property⟩)
  · intro s r x hx
    have hxC := space_subset_of_le (hLC s) x.property
    rw [hGlocal s r ⟨x, hxC⟩ hx]
    exact hHD s r ⟨x, (hLS s).subset x.property⟩
  · intro x
    obtain ⟨s, hs⟩ := mem_iUnion.mp
      ((space_iUnionOfCompatible C hcross).subset (hTS.symm.subset x.property))
    exact (hGlocal s 0 ⟨x, hs⟩ x.property).trans (hH0 s ⟨x, (hCS s).subset hs⟩)
  · intro x
    exact hG1 ⟨x, hTS.symm.subset x.property⟩
  · exact hTS ▸ hqPL

end PoincareConjecture.M76
