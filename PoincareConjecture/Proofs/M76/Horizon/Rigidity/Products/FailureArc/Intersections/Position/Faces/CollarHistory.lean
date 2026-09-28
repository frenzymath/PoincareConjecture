import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Initial.FiniteEdges
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Faces.RetainedHistory








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_collar_protected_planar_triangle_history
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Z rimMark : Set X}
    (Source : SimplicialComplex ℝ (ℝ × ℝ)) (hSource : Source.faces.Finite)
    {f : (ℝ × ℝ) → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hfi : InjOn f Source.space)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K M : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hMK : M ≤ K)
    (hMdim : ∀ a ∈ M.faces, a.card ≤ 3)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    (hprotectedV : Disjoint (f '' Source.space ∩ Z) (g '' K.vertices))
    (faces : Finset (K.FaceOfCard 3))
    (hprotectedE : ∀ a ∈ M.faces, a.card = 2 → (∃ s ∈ faces, a ⊆ s.1) →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set E))).Finite ∧
        HasOriginalEdgeCofaceCharts e (f '' Source.space) K g a)
    (hrimMark : rimMark ⊆ Z)
    (hrim : ∀ x ∈ Source.space, x ∉ interior Source.space → f x ∈ rimMark)
    (hactive : ∀ s ∈ faces, s.1 ∉ M.faces)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s ∈ faces, ∀ i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (hQmark : ∀ s ∈ faces, Disjoint (Q s).source rimMark)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s ∈ faces, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s ∈ faces, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E))) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ EqOn F id W ∧ g '' M.space ⊆ W ∧ EqOn F id rimMark ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧
      (∀ x ∈ Source.space, x ∉ interior Source.space → F (f x) = f x) ∧
      Disjoint (F '' (f '' Source.space)) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 → (a ∉ M.faces ∨ ∃ s ∈ faces, a ⊆ s.1) →
        (F '' (f '' Source.space) ∩ g '' convexHull ℝ (a : Set E)).Finite ∧
        HasOriginalEdgeCofaceCharts e (F '' (f '' Source.space)) K g a) ∧
      ∀ s ∈ faces, InTriangleGraphPosition (Q s) (F '' (f '' Source.space))
        (g '' convexHull ℝ (s.1 : Set E)) (convexHull ℝ ((A s) '' (s.1 : Set E))) := by
  obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, hfF, hFV, hedges⟩ :=
    exists_protected_planar_finite_edge_coface_position Source hSource hf hcover he
      K M hK hMK g hgc hgi hstars hZ hmark hprotectedV
      (fun a => a ∉ M.faces ∨ ∃ s ∈ faces, a ⊆ s.1)
      (fun a ha hc hel => hprotectedE a ha hc (hel.resolve_left (not_not.mpr ha)))
  have hFZ : EqOn F id Z := fun _ hx =>
    hFout (fun hc => disjoint_left.mp hCZ hc hx)
  have hFimage : (F ∘ f) '' Source.space = F '' (f '' Source.space) :=
    (image_image F f Source.space).symm
  obtain ⟨G, W, hW, hGW, hGZ, hotherW, hskW, hGPL, hGinv, _, _, hpositions⟩ :=
    exists_finite_planar_triangle_position_with_retained_faces Source hSource hfF
      (fun x hx y hy hxy => hfi hx hy (F.injective hxy)) hcover he K hK g hgc hgi
      (by rw [hFimage]; exact hFV) faces
      (by intro s hs a ha has hc; rw [hFimage]; exact (hedges a ha hc (Or.inr ⟨s, hs, has⟩)).1)
      (by intro s hs a ha has hc; rw [hFimage]; exact (hedges a ha hc (Or.inr ⟨s, hs, has⟩)).2)
      rimMark (by
        intro x hx hn
        change F (f x) ∈ rimMark
        simpa only [hFZ (hrimMark (hrim x hx hn)), id_eq] using hrim x hx hn)
      Q hQ hQmark A hmap hA
  have hPL := original_PL_motion_trans_both e hcover F G hFPL hFinv hGPL hGinv
  have himage : (F.trans G) '' (f '' Source.space) = G '' (F '' (f '' Source.space)) := by
    rw [image_image G F]
    rfl
  have hfix : EqOn (F.trans G) id rimMark := by
    intro x hx
    change G (F x) = x
    simpa only [hFZ (hrimMark hx), id_eq] using hGZ hx
  have hsame (x : X) (hx : x ∈ W) :
      x ∈ G '' (F '' (f '' Source.space)) ↔ x ∈ F '' (f '' Source.space) := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact G.injective (heq.trans (hGW hx).symm) ▸ hy
    · exact fun hy => ⟨x, hy, hGW hx⟩
  have hcollar : g '' M.space ⊆ Cᶜ ∩ W := by
    rintro _ ⟨x, hx, rfl⟩
    have hxZ : g x ∈ Z := (hmark x (SimplicialComplex.space_subset_of_le hMK hx)).mpr hx
    refine ⟨fun hc => disjoint_left.mp hCZ hc hxZ, ?_⟩
    obtain ⟨a, ha, hxa⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact hotherW a (hMK ha) (hMdim a ha)
      (fun s hs heq => hactive s hs (heq.symm ▸ ha)) ⟨x, hxa, rfl⟩
  have hfixNeighborhood : EqOn (F.trans G) id (Cᶜ ∩ W) := by
    intro x hx
    change G (F x) = x
    simpa only [hFout hx.1, id_eq] using hGW hx.2
  refine ⟨F.trans G, Cᶜ ∩ W, hC.isClosed.isOpen_compl.inter hW,
    hfixNeighborhood, hcollar, hfix, hPL.1, hPL.2,
    hf.comp_chart_homeomorph Source hSource (F.trans G) hcover hPL.1,
    fun x hx hn => hfix (hrim x hx hn), ?_, ?_, ?_⟩
  · rw [himage]
    apply disjoint_left.mpr
    intro x hx hv
    obtain ⟨v, hvK, rfl⟩ := hv
    have hvW : g v ∈ W := hskW {v} hvK (by simp) (by simp)
    exact disjoint_left.mp hFV ((hsame (g v) hvW).mp hx) ⟨v, hvK, rfl⟩
  · intro a ha hc hel
    have heW := hskW a ha hc.le
    have heq : (F.trans G) '' (f '' Source.space) ∩ g '' convexHull ℝ (a : Set E) =
        F '' (f '' Source.space) ∩ g '' convexHull ℝ (a : Set E) := by
      rw [himage]
      ext x
      exact and_congr_left (fun hx => hsame x (heW hx))
    refine ⟨heq.symm ▸ (hedges a ha hc hel).1, ?_⟩
    rw [himage]
    apply (hedges a ha hc hel).2.image_of_disjoint_support G hW.isClosed_compl
    · exact disjoint_left.mpr (fun x hx he => hx (heW he))
    · simpa only [compl_compl] using hGW
  · intro s hs
    simpa only [himage, hFimage] using hpositions s hs

end PoincareConjecture.M76
