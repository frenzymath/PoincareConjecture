import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ControlledOriginalSkeleton
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.SharedFaceBoundaryPrograms
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.FiniteFaceConeHomotopy
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalSkeletonFrontierCrossings
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalConeEdgeMarks
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalSkeletonBoundaryFixed











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
  [TopologicalSpace X] [Nonempty X]

variable (K : SimplicialComplex ℝ E)

local notation "Edges" => {s : K.faces // Finset.card (Subtype.val s) = 2}
local notation "Faces" => {s : K.faces // Finset.card (Subtype.val s) = 3}

theorem PLDomain.exists_original_disk_cone_homotopy
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (f : E → X) (hfY : MapsTo f K.space Y)
    (B : K.vertices → OpenPartialHomeomorph X V3)
    (hcompat : ∀ v i, (e i).symm.trans (B v) ∈ piecewiseAffineGroupoid V3)
    (hsource : ∀ v : K.vertices, MapsTo f (K.closedStar v).space (B v).source)
    (hcoord : ∀ v : K.vertices, (K.closedStar v).AffineOnFaces (B v ∘ f))
    (hkind : ∀ v, Disjoint (B v).source F ∨ ∃ ell : V3 →ᴬ[ℝ] ℝ,
      (∀ y ∈ (B v).source, y ∈ N ↔ 0 ≤ ell (B v y)) ∧
      ∀ y ∈ (B v).source, y ∈ F ↔ ell (B v y) = 0) :
    ∃ (a b : Edges → K.vertices) (v : Faces → K.vertices)
      (T0 R : SimplicialComplex ℝ E) (L : Faces → SimplicialComplex ℝ E)
      (Q : Edges → SimplicialComplex ℝ E) (C : Faces → SimplicialComplex ℝ E)
      (T : SimplicialComplex ℝ E) (G0 : C(I × T0.space, X))
      (G : C(I × K.space, X)) (g0 g : E → X) (p : K.vertices → C(I, X)),
      (∀ k, (a k : E) ≠ b k) ∧
      (∀ k, ({(a k : E), (b k : E)} : Finset E) = k.val.val) ∧
      (∀ s, (v s : E) ∈ s.val.val) ∧
      T0.faces.Finite ∧ T0 ≤ K ∧ T0.space = ⋃ k, segment ℝ (a k : E) (b k : E) ∧
      R.faces.Finite ∧ R.IsSubdivision T0 ∧
      (∀ s, L s ≤ R ∧ (L s).space = frontier (convexHull ℝ (s.val.val : Set E)) ∧
        (∀ z ∈ R.faces, (∀ x ∈ z, x ∈ (L s).vertices) → z ∈ (L s).faces)) ∧
      (∀ k, Q k ≤ R ∧ (Q k).space = segment ℝ (a k : E) (b k : E) ∧
        ∀ z ∈ R.faces, (∀ x ∈ z, x ∈ (Q k).vertices) → z ∈ (Q k).faces) ∧
      T.faces.Finite ∧ T.space = K.space ∧ T.faces = ⋃ s, (C s).faces ∧
      (∀ s, (C s).faces.Finite ∧ (C s).space = convexHull ℝ (s.val.val : Set E) ∧
        L s ≤ C s ∧ C s ≤ T ∧
        (C s).vertices = insert (s.val.val.centroid ℝ id) (L s).vertices ∧
        (∀ z ∈ (L s).faces, insert (s.val.val.centroid ℝ id) z ∈ (C s).faces) ∧
        (∀ z, z ∈ (C s).faces ↔ z.Nonempty ∧
          (z.erase (s.val.val.centroid ℝ id) = ∅ ∨ z.erase (s.val.val.centroid ℝ id) ∈ (L s).faces)) ∧
        (C s).AffineOnFaces (B (v s) ∘ g) ∧ g (s.val.val.centroid ℝ id) ∉ F ∧
        EqOn g g0 (frontier (convexHull ℝ (s.val.val : Set E))) ∧
        MapsTo g (C s).space (B (v s)).source) ∧
      (∀ w, p w 0 = f w) ∧ (∀ w t, p w t ∈ Y) ∧
      (∀ w : K.vertices, f w ∉ F → ∀ t, p w t = f w) ∧
      (∀ w (t : I), 0 < (t : ℝ) → p w t ∉ F) ∧
      (∀ w : K.vertices, g0 w ∉ F) ∧
      (∀ k, (segment ℝ (a k : E) (b k : E) ∩ g0 ⁻¹' F).Subsingleton) ∧
      (∀ z ∈ T.faces, z.card = 2 → ∃ x ∈ z, g x ∉ F) ∧
      (∀ k (t r : I) (hx : AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈ T0.space),
        G0 (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩) ∈ (B (a k)).source ∧
        B (a k) (G0 (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩)) =
          AffineMap.lineMap (B (a k) (p (a k) t)) (B (a k) (p (b k) t)) (r : ℝ)) ∧
      (∀ k (t : I) (ha : (a k : E) ∈ T0.space) (hb : (b k : E) ∈ T0.space),
        G0 (t, ⟨a k, ha⟩) = p (a k) t ∧ G0 (t, ⟨b k, hb⟩) = p (b k) t) ∧
      (∀ x : T0.space, G0 (0, x) = f x) ∧ (∀ x : T0.space, G0 (1, x) = g0 x) ∧
      (∀ s (t : I) (x : (L s).space) (hxK : (x : E) ∈ K.space) (hxT : (x : E) ∈ T0.space),
        G (t, ⟨x, hxK⟩) = G0 (t, ⟨x, hxT⟩)) ∧
      ((∀ x ∈ frontier K.space, f x ∉ F) →
        (∀ (t : I) (x : K.space), (x : E) ∈ frontier K.space → G (t, x) = f x) ∧
        EqOn g f (frontier K.space) ∧ (∀ x ∈ frontier K.space, g x ∉ F)) ∧
      (∀ z, G z ∈ Y) ∧ (∀ x : K.space, G (0, x) = f x) ∧
      (∀ x : K.space, G (1, x) = g x) ∧ PolyhedralPLInCharts e g K.space := by
  classical
  let : Finite K.faces := hK.to_subtype
  obtain ⟨a, b, v, W, T0, G0, g0, p, hab, hpair, hv, hW, hT0, hT0K, hT0S,
    hp0, hpY, hpfix, hpoff, hG0Y, hformula, hcontrol, hend, hG00, hG01, hg0⟩ :=
    hN.exists_controlled_original_skeleton hY hcut K hK f hfY B hcompat hsource hcoord
  obtain ⟨R, L, Q, Ds, hR, hRT, hL, hQ, hboundaryT, hDs, hDs0, hDs1, hDscontrol⟩ :=
    K.exists_shared_face_boundary_programs hK hdim a b hab hpair T0 hT0 hT0S G0
      f g0 hG00 hG01 hg0 (fun s => B (v s)) (fun s => hcompat (v s)) W hcontrol
  let D : C(I × R.space, X) := G0.comp
    ⟨fun z => (z.1, ⟨z.2, hRT.space_eq.subset z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩
  have hDcontrol (s : Faces) (t : I) (x : (L s).space) :
      D (t, ⟨x, space_subset_of_le (hL s).1 x.property⟩) ∈ (B (v s)).source ∧
      B (v s) (D (t, ⟨x, space_subset_of_le (hL s).1 x.property⟩)) ∈ W s := by
    have hx : (x : E) ∈ frontier (convexHull ℝ (s.val.val : Set E)) := (hL s).2.1.subset x.property
    have hh := hDscontrol s (t, ⟨x, hx⟩)
    rw [hDs s t ⟨x, hx⟩ (hboundaryT s hx)] at hh
    exact hh
  have hstar (s : Faces) : s.val.val ∈ (K.closedStar (v s)).faces := by
    refine ⟨s.val.property, ?_⟩
    simpa only [Finset.insert_eq_of_mem (hv s)] using s.val.property
  choose A hA using fun s : Faces => hcoord (v s) s.val.val (hstar s)
  have hfW (s : Faces) : MapsTo (A s) (convexHull ℝ (s.val.val : Set E)) (W s) := by
    intro x hx
    rw [← hA s hx]
    exact (hW s).2.2.2.2 hx
  obtain ⟨C, T, G, g, hT, hTK, hTfaces, hC, hGcontrol, hGD, hG0, hG1, hg⟩ :=
    hN.exists_finite_face_cone_homotopy hY hcut K hK hdim hcv hne R hR L
      (fun s => (hL s).1) (fun s => (hL s).2.1) (fun s => B (v s))
      (fun s => hcompat (v s)) f g0 A
      (fun s _ hx => hsource (v s) (convexHull_subset_space (hstar s) hx)) hA
      (fun s => (hL s).2.2.2) W (fun s => (hW s).1) (fun s => (hW s).2.1)
      (fun s => (hW s).2.2.1) (fun s => (hW s).2.2.2.1) hfW D hDcontrol
      (fun x => hG00 ⟨x, hRT.space_eq.subset x.property⟩)
      (fun x => hG01 ⟨x, hRT.space_eq.subset x.property⟩)
  have hkindF (w : K.vertices) : Disjoint (B w).source F ∨ ∃ ell : V3 →ᴬ[ℝ] ℝ,
      ∀ y ∈ (B w).source, y ∈ F ↔ ell (B w y) = 0 := by
    rcases hkind w with hd | ⟨ell, _, hf⟩
    · exact Or.inl hd
    · exact Or.inr ⟨ell, hf⟩
  obtain ⟨hg0off, hcross, _⟩ := K.original_skeleton_frontier_crossings hK hdim hcv hne
    a b hpair T0 hT0S G0 g0 p (fun w => hpoff w 1 (by norm_num)) hG01 hend B hformula hkindF
  have hQhull (k : Edges) : (Q k).space = convexHull ℝ (k.val.val : Set E) := by
    rw [← hpair k, Finset.coe_pair, convexHull_pair]
    exact (hQ k).2.1
  have hnozero : ∀ z ∈ T.faces, z.card = 2 → ∃ x ∈ z, g x ∉ F := by
    apply original_cone_edges_have_unmarked_vertices K R T hdim L C Q
      (fun s => (hL s).1) (fun s => (hL s).2.1) (fun k => (hQ k).1) hQhull hTfaces
    · intro s
      obtain ⟨_, _, _, _, _, _, hf, _⟩ := hC s
      exact hf
    · intro s
      obtain ⟨_, _, _, _, _, _, _, _, _, hb, _⟩ := hC s
      exact hb
    · intro s
      obtain ⟨_, _, _, _, _, _, _, _, ha, _⟩ := hC s
      exact ha
    · intro x hx
      exact hg0off ⟨x, hx⟩
    · intro z hz hc x hx hxF y hy hyF
      let k : Edges := ⟨⟨z, hz⟩, hc⟩
      have hseg : convexHull ℝ (z : Set E) = segment ℝ (a k : E) (b k : E) := by
        rw [show z = k.val.val from rfl, ← hpair k, Finset.coe_pair, convexHull_pair]
      exact hcross k ⟨hseg.subset hx, hxF⟩ ⟨hseg.subset hy, hyF⟩
  refine ⟨a, b, v, T0, R, L, Q, C, T, G0, G, g0, g, p, hab, hpair, hv,
    hT0, hT0K, hT0S, hR, hRT, fun s => ⟨(hL s).1, (hL s).2.1, (hL s).2.2.1⟩,
    hQ, hT, hTK, hTfaces, ?_, hp0, hpY, hpfix, hpoff, hg0off, hcross, hnozero,
    hformula, hend, hG00, hG01,
    ?_, ?_, ?_, hG0, hG1, hg⟩
  · intro s
    obtain ⟨hc, hs, hl, ht, hv, hcone, hfaces, hcoords, hoff, hbound, hmap⟩ := hC s
    exact ⟨hc, hs, hl, ht, hv, hcone, hfaces, hcoords, hoff, hbound, fun _ hx => (hmap _ hx).1⟩
  · intro s t x hxK hxT
    exact hGD s t x hxK
  · intro hboundary
    have hfixed := original_skeleton_fixes_boundary K hK hdim hcv hne a b hpair
      T0 hT0S G0 f p F hboundary hpfix B hsource hcoord hformula hend
    have hwhole (t : I) (x : K.space) (hx : (x : E) ∈ frontier K.space) : G (t, x) = f x := by
      obtain ⟨s, hs, hsc, hxs⟩ := K.exists_full_face_of_mem_convex_space hK hcv hne x.property
      have hsc3 : s.card = 3 := by omega
      let si : Faces := ⟨⟨s, hs⟩, hsc3⟩
      have hxf : (x : E) ∈ frontier (convexHull ℝ (si.val.val : Set E)) :=
        ⟨subset_closure hxs, fun h => hx.2 (interior_mono (K.convexHull_subset_space hs) h)⟩
      have hxL : (x : E) ∈ (L si).space := (hL si).2.1.symm.subset hxf
      exact (hGD si t ⟨x, hxL⟩ x.property).trans (hfixed t ⟨x, hboundaryT si hxf⟩ hx)
    have hgf : EqOn g f (frontier K.space) := by
      intro x hx
      have hxK : x ∈ K.space := (K.isCompact_space_of_finite hK).isClosed.closure_eq ▸ hx.1
      exact (hG1 ⟨x, hxK⟩).symm.trans (hwhole 1 ⟨x, hxK⟩ hx)
    exact ⟨hwhole, hgf, fun x hx => hgf hx ▸ hboundary x hx⟩
  · rintro ⟨t, x⟩
    have hxT : (x : E) ∈ T.space := hTK.symm.subset x.property
    have hxC : (x : E) ∈ ⋃ s, (C s).space := by
      obtain ⟨r, hr, hxr⟩ := mem_space_iff.mp hxT
      rw [hTfaces] at hr
      obtain ⟨s, hs⟩ := mem_iUnion.mp hr
      exact mem_iUnion.mpr ⟨s, convexHull_subset_space hs hxr⟩
    obtain ⟨s, hs⟩ := mem_iUnion.mp hxC
    exact (hGcontrol s t ⟨x, hs⟩ x.property).2.2

end PoincareConjecture.M76
