import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.ComponentMatching
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.ComponentComplement



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
noncomputable local instance : DecidableEq P2 := fun _ _ => Classical.propDecidable _

open Classical in
theorem SurfaceIntersectionComponents.exists_matched_interval_endpoints
    {X : Type*} {J K q B : Set P2} {f g : P2 → X}
    (C : SurfaceIntersectionComponents J K f g B)
    (M : SurfaceIntersectionComponents K J g f q)
    (hfi : InjOn f J) (hgi : InjOn g K)
    (hrims : ∀ x ∈ J, ∀ y ∈ K, f x = g y → (x ∈ q ↔ y ∈ B))
    (harcs : ∀ j, IsFinitePLBallPair ℝ (M.pieces j) (M.pieces j ∩ q))
    (i : C.right.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ j, ∃ a b c d : P2,
      a ≠ b ∧ c ≠ d ∧
      IsFinitePLBallPair ℝ (M.pieces j) {a,b} ∧
      IsFinitePLBallPair ℝ (C.pieces i) {c,d} ∧
      M.pieces j ∩ q = {a,b} ∧ C.pieces i ∩ B = {c,d} ∧
      a ∈ q ∧ b ∈ q ∧ c ∈ B ∧ d ∈ B ∧
      M.pieces j \ {a,b} ⊆ J \ q ∧ C.pieces i \ {c,d} ⊆ K \ B ∧
      f '' M.pieces j = g '' C.pieces i ∧ f a = g c ∧ f b = g d ∧
      IsClosed ((J ∩ f ⁻¹' (g '' K)) \ M.pieces j) := by
  obtain ⟨H,hH⟩ := C.exists_component_equiv M
  let j := H.symm i
  have hphys : f '' M.pieces j = g '' C.pieces i := by
    rw [hH]
    simp only [j,H.apply_symm_apply]
  have hMsub : M.pieces j ⊆ J := fun x hx =>
    (M.right_space.subset (M.cover.symm.subset (mem_iUnion.mpr ⟨j,hx⟩))).1
  have hCsub : C.pieces i ⊆ K := fun x hx =>
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨i,hx⟩))).1
  obtain ⟨a,b,hab,hends⟩ := (harcs j).exists_boundary_eq_pair
  have ha := hends.symm.subset (show a ∈ ({a,b}:Set P2) from Or.inl rfl)
  have hb := hends.symm.subset (show b ∈ ({a,b}:Set P2) from Or.inr rfl)
  obtain ⟨c,hc,hca⟩ := hphys.subset (mem_image_of_mem f ha.1)
  obtain ⟨d,hd,hdb⟩ := hphys.subset (mem_image_of_mem f hb.1)
  have hcB := (hrims a (hMsub ha.1) c (hCsub hc) hca.symm).mp ha.2
  have hdB := (hrims b (hMsub hb.1) d (hCsub hd) hdb.symm).mp hb.2
  have hcd : c ≠ d := by
    intro h
    apply hab
    apply hfi (hMsub ha.1) (hMsub hb.1)
    exact hca.symm.trans ((congrArg g h).trans hdb)
  have hCends : C.pieces i ∩ B = {c,d} := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hphys.symm.subset (mem_image_of_mem g hy.1)
      have hxq := (hrims x (hMsub hx) y (hCsub hy.1) hxy).mpr hy.2
      rcases hends.subset ⟨hx,hxq⟩ with hx | hx
      · left
        apply hgi (hCsub hy.1) (hCsub hc)
        exact hxy.symm.trans ((congrArg f hx).trans hca.symm)
      · right
        apply hgi (hCsub hy.1) (hCsub hd)
        exact hxy.symm.trans ((congrArg f hx).trans hdb.symm)
    · rintro y (rfl | rfl)
      · exact ⟨hc,hcB⟩
      · exact ⟨hd,hdB⟩
  have hCball : IsFinitePLBallPair ℝ (C.pieces i) {c,d} := by
    rcases C.models i with h | ⟨_,_,_,_,_,hno⟩
    · exact hCends ▸ h
    · exact (disjoint_left.mp hno hc hcB).elim
  refine ⟨j,a,b,c,d,hab,hcd,hends ▸ harcs j,hCball,hends,hCends,
    ha.2,hb.2,hcB,hdB,?_,?_,hphys,hca.symm,hdb.symm,M.isClosed_complement_piece j⟩
  · exact fun x hx => ⟨hMsub hx.1,fun hxq => hx.2 (hends.subset ⟨hx.1,hxq⟩)⟩
  · exact fun x hx => ⟨hCsub hx.1,fun hxB => hx.2 (hCends.subset ⟨hx.1,hxB⟩)⟩

open Classical in
theorem SurfaceIntersectionComponents.interval_models_of_paired_intervals
    {X : Type*} {J K q B : Set P2} {f g : P2 → X}
    (C : SurfaceIntersectionComponents J K f g B)
    (M : SurfaceIntersectionComponents K J g f q)
    (hfi : InjOn f J) (hgi : InjOn g K)
    (hrims : ∀ x ∈ J, ∀ y ∈ K, f x = g y → (x ∈ q ↔ y ∈ B))
    (harcs : ∀ j, IsFinitePLBallPair ℝ (M.pieces j) (M.pieces j ∩ q)) :
    ∀ i, IsFinitePLBallPair ℝ (C.pieces i) (C.pieces i ∩ B) := by
  intro i
  obtain ⟨_,_,_,_,_,_,_,_,hball,_,heq,_⟩ :=
    C.exists_matched_interval_endpoints M hfi hgi hrims harcs i
  exact heq.symm ▸ hball

end PoincareConjecture.M76
