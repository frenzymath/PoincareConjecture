import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Faces.CollarHistory
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.Relative
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_collar_protected_whole_planar_position
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Z rimMark : Set X}
    (Source : SimplicialComplex ℝ V2) (hSource : Source.faces.Finite)
    {f : V2 → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hfi : InjOn f Source.space)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K M : SimplicialComplex ℝ V2) (hK : K.faces.Finite) (hMK : M ≤ K)
    (g : V2 → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hg : PolyhedralPLInCharts e g K.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    (hprotectedV : Disjoint (f '' Source.space ∩ Z) (g '' K.vertices))
    (faces : Finset (K.FaceOfCard 3))
    (hprotectedE : ∀ a ∈ M.faces, a.card = 2 → (∃ s ∈ faces, a ⊆ s.1) →
      (f '' Source.space ∩ (g '' convexHull ℝ (a : Set V2))).Finite ∧
        HasOriginalEdgeCofaceCharts e (f '' Source.space) K g a)
    (hrimMark : rimMark ⊆ Z)
    (hrim : ∀ x ∈ Source.space, x ∉ interior Source.space → f x ∈ rimMark)
    (hactive : ∀ s ∈ faces, s.1 ∉ M.faces)
    (hfaces : ∀ s : K.FaceOfCard 3, s.1 ∉ M.faces → s ∈ faces)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s ∈ faces, ∀ i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (hQmark : ∀ s ∈ faces, Disjoint (Q s).source rimMark)
    (A : K.FaceOfCard 3 → V2 →ᴬ[ℝ] V3)
    (hmap : ∀ s ∈ faces, MapsTo g (convexHull ℝ (s.1 : Set V2)) (Q s).source)
    (hA : ∀ s ∈ faces, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set V2)))
    (hboundaryM : K.space \ interior K.space ⊆ M.space)
    (hboundary : ∀ x ∈ K.space \ interior K.space, g x ∈ f '' Source.space →
      Nonempty (OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) true))
    (hcollar : ∀ x ∈ M.space, x ∈ interior K.space → g x ∈ f '' Source.space →
      Nonempty (OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) false)) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ EqOn F id W ∧ g '' M.space ⊆ W ∧ EqOn F id rimMark ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      PolyhedralPLInCharts e (F ∘ f) Source.space ∧
      InjOn (F ∘ f) Source.space ∧
      (∀ x ∈ Source.space, x ∉ interior Source.space → F (f x) = f x) ∧
      (∀ x ∈ K.space \ interior K.space, g x ∈ (F ∘ f) '' Source.space →
        Nonempty (OriginalSurfacePairChart e ((F ∘ f) '' Source.space)
          (g '' K.space) (g x) true)) ∧
      (∀ x ∈ interior K.space, g x ∈ (F ∘ f) '' Source.space →
        Nonempty (OriginalSurfacePairChart e ((F ∘ f) '' Source.space)
          (g '' K.space) (g x) false)) ∧
      Nonempty (SurfaceIntersectionComponents Source.space K.space (F ∘ f) g
        (K.space \ interior K.space)) := by
  classical
  have hMdim (a : Finset V2) (ha : a ∈ M.faces) : a.card ≤ 3 := by
    have hc := (M.indep ha).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe, Module.finrank_prod, Module.finrank_self, Nat.reduceAdd] using hc
  obtain ⟨F, W, hW, hfix, hMW, hFmark, hPL, hInv, hfF, hrimF, hFV, hedges, hpos⟩ :=
    exists_collar_protected_planar_triangle_history Source hSource hf hfi hcover he
      K M hK hMK hMdim g hgc hgi hstars hZ hmark hprotectedV faces hprotectedE
      hrimMark hrim hactive Q hQ hQmark A hmap hA
  have himage : (F ∘ f) '' Source.space = F '' (f '' Source.space) :=
    (image_image F f Source.space).symm
  have hboundaryF : ∀ x ∈ K.space \ interior K.space, g x ∈ (F ∘ f) '' Source.space →
      Nonempty (OriginalSurfacePairChart e ((F ∘ f) '' Source.space)
        (g '' K.space) (g x) true) := by
    intro x hx hxf
    rw [himage] at hxf ⊢
    exact exists_retained_boundary_pair_chart F hW hfix
      (hMW (mem_image_of_mem g (hboundaryM hx))) (hboundary x hx) hxf
  have hinteriorF : ∀ x ∈ interior K.space, g x ∈ (F ∘ f) '' Source.space →
      Nonempty (OriginalSurfacePairChart e ((F ∘ f) '' Source.space)
        (g '' K.space) (g x) false) := by
    intro x hx hxf
    rw [himage] at hxf ⊢
    exact exists_relative_whole_planar_interior_chart K M hK hgc hgi F W hW hfix
      hMW hcollar hFV (fun a ha hc hnot => (hedges a ha hc (Or.inl hnot)).2)
      faces hfaces Q hQ A hmap hA hpos hx hxf
  have hFi : InjOn (F ∘ f) Source.space := fun x hx y hy hxy => hfi hx hy (F.injective hxy)
  refine ⟨F, W, hW, hfix, hMW, hFmark, hPL, hInv, hfF, hFi, hrimF,
    hboundaryF, hinteriorF, ?_⟩
  apply nonempty_surface_intersection_components he Source K hSource hK hfF hg hFi hgi
    (K.space \ interior K.space)
  · intro x hx
    exact hboundaryF x hx.2
  · intro x hx
    exact hinteriorF x (by by_contra hn; exact hx.2 ⟨hx.1, hn⟩)

end PoincareConjecture.M76
