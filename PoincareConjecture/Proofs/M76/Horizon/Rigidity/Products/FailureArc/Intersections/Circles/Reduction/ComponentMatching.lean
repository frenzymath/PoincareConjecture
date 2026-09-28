import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.PairedComponents
import Mathlib.Topology.Homeomorph.Lemmas



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.SurfaceIntersectionComponents

open Classical in
theorem exists_component_equiv
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {T : Set F} {f : E → X} {g : F → X} {Q : Set E} {R : Set F}
    (C : SurfaceIntersectionComponents S T f g R)
    (D : SurfaceIntersectionComponents T S g f Q) :
    ∃ c : D.right.vertexAbstractComplex.edgeGraph.ConnectedComponent ≃
        C.right.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      ∀ i, f '' D.pieces i = g '' C.pieces (c i) := by
  classical
  let H := (Homeomorph.setCongr (D.right_space.trans C.left_space.symm)).trans C.matching
  have hHvalue (x : D.right.space) : f x = g (H x) :=
    C.matching_value ⟨x,(D.right_space.trans C.left_space.symm).subset x.property⟩
  let K := H.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y => by
    have hfiber : H ⁻¹' {y} = {H.symm y} := by
      ext x
      exact H.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton
  let c := D.intrinsic.symm.trans (K.toEquiv.trans C.intrinsic)
  have hvalue (x : D.right.space) :
      C.intrinsic (ConnectedComponents.mk (H x)) =
        c (D.intrinsic (ConnectedComponents.mk x)) := by
    simp only [c,Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  have hmem (x : D.right.space) (i) : (x : E) ∈ D.pieces i ↔
      (H x : F) ∈ C.pieces (c i) := by
    rw [←D.intrinsic_value,←C.intrinsic_value,hvalue,c.injective.eq_iff]
  refine ⟨c,fun i => ?_⟩
  apply Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    have hxD : x ∈ D.right.space := D.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩)
    exact ⟨H ⟨x,hxD⟩,(hmem ⟨x,hxD⟩ i).mp hx,(hHvalue ⟨x,hxD⟩).symm⟩
  · rintro z ⟨y,hy,rfl⟩
    have hyC : y ∈ C.right.space := C.cover.symm.subset (mem_iUnion.mpr ⟨c i,hy⟩)
    have hpre : (H.symm ⟨y,hyC⟩ : E) ∈ D.pieces i := by
      apply (hmem (H.symm ⟨y,hyC⟩) i).mpr
      simpa only [H.apply_symm_apply] using hy
    refine ⟨H.symm ⟨y,hyC⟩,hpre,?_⟩
    simpa only [H.apply_symm_apply] using hHvalue (H.symm ⟨y,hyC⟩)

end PoincareConjecture.M76.SurfaceIntersectionComponents
