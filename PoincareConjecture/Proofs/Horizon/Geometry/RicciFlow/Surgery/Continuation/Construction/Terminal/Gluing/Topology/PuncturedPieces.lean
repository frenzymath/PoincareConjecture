import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.LocalModel.Homeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Inclusions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

abbrev puncturedPiece (j : Option ι) : Type u :=
  Piece U (fun i => {x : (R i).output.carrier // x ≠ (R i).tip}) j

def puncturedInclusion : ∀ j, puncturedPiece I R U j → (cutCarrier I R U hU hd hc).carrier
  | none => retainedInclusion I R U hU hd hc
  | some i => fun x => capInclusion I R U hU hd hc i x.val

def puncturedOriginal : ∀ j, puncturedPiece I R U j → S.carrier
  | none => Subtype.val
  | some i => fun x => ((R i).puncturedNeckHomeomorph x).val

theorem puncturedInclusion_openEmbedding (j : Option ι) :
    IsOpenEmbedding (puncturedInclusion I R U hU hd hc j) := by
  cases j with
  | none => exact retainedInclusion_openEmbedding I R U hU hd hc
  | some i =>
    exact (capInclusion_openEmbedding I R U hU hd hc i).comp
      isOpen_ne.isOpenEmbedding_subtypeVal

omit [Countable ι] in
theorem puncturedOriginal_openEmbedding (j : Option ι) :
    IsOpenEmbedding (puncturedOriginal I R U j) := by
  cases j with
  | none => exact U.isOpen.isOpenEmbedding_subtypeVal
  | some i => exact (R i).puncturedNeckHomeomorph_openEmbedding

variable (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (hUn : ∀ i, (U : Set S.carrier) ∩ (I i).neck.carrier = (I i).negativeHalf)

include hUn in
theorem puncturedOriginal_retained_eq_iff (i : ι) (x : U)
    (y : {y : (R i).output.carrier // y ≠ (R i).tip}) :
    x.val = ((R i).puncturedNeckHomeomorph y).val ↔
      retainedInclusion I R U hU hd hc x = capInclusion I R U hU hd hc i y.val := by
  constructor
  · intro hxy
    have hx : x.val ∈ (I i).negativeHalf := by
      change x.val ∈ ((I i).negativeHalf : Set S.carrier)
      rw [← hUn i]
      refine ⟨x.property, ?_⟩
      rw [hxy]
      exact ((R i).puncturedNeckHomeomorph y).property
    have hy : y.val = (R i).collapse x.val := by
      have he : (R i).puncturedNeckHomeomorph y =
          (R i).puncturedNeckHomeomorph
            ⟨(R i).collapse x.val, (R i).collapse_negative_ne_tip hx⟩ := by
        apply Subtype.ext
        rw [(R i).puncturedNeckHomeomorph_collapse x.val hx]
        exact hxy.symm
      exact congrArg Subtype.val ((R i).puncturedNeckHomeomorph.injective he)
    rw [hy]
    exact retainedInclusion_eq_cap I R U hU hd hc i x hx
  · intro hxy
    have hx := (retainedInclusion_mem_cap_iff I R U hU hd hc i x).mp ⟨y.val, hxy.symm⟩
    have hy : (R i).collapse x.val = y.val :=
      (capInclusion_openEmbedding I R U hU hd hc i).injective
        ((retainedInclusion_eq_cap I R U hU hd hc i x hx).symm.trans hxy)
    have he : y = ⟨(R i).collapse x.val, (R i).collapse_negative_ne_tip hx⟩ := Subtype.ext hy.symm
    rw [he, (R i).puncturedNeckHomeomorph_collapse x.val hx]

include hneck hUn in
theorem puncturedOriginal_eq_iff (i j : Option ι)
    (x : puncturedPiece I R U i) (y : puncturedPiece I R U j) :
    puncturedOriginal I R U i x = puncturedOriginal I R U j y ↔
      puncturedInclusion I R U hU hd hc i x = puncturedInclusion I R U hU hd hc j y := by
  cases i with
  | none =>
    cases j with
    | none =>
      exact (Subtype.ext_iff).symm.trans
        (retainedInclusion_openEmbedding I R U hU hd hc).injective.eq_iff.symm
    | some j => exact puncturedOriginal_retained_eq_iff I R U hU hd hc hUn j x y
  | some i =>
    cases j with
    | none =>
      exact eq_comm.trans ((puncturedOriginal_retained_eq_iff I R U hU hd hc hUn i y x).trans eq_comm)
    | some j =>
      by_cases hij : i = j
      · subst j
        exact (puncturedOriginal_openEmbedding I R U (some i)).injective.eq_iff.trans
          (puncturedInclusion_openEmbedding I R U hU hd hc (some i)).injective.eq_iff.symm
      · constructor
        · intro hxy
          change ((R i).puncturedNeckHomeomorph x).val =
            ((R j).puncturedNeckHomeomorph y).val at hxy
          exact False.elim (Set.disjoint_left.mp (hneck hij)
            ((R i).puncturedNeckHomeomorph x).property
            (by rw [hxy]; exact ((R j).puncturedNeckHomeomorph y).property))
        · intro hxy
          exact False.elim (Set.disjoint_left.mp (capInclusion_disjoint I R U hU hd hc hij)
            ⟨x.val, rfl⟩ ⟨y.val, hxy.symm⟩)

end PoincareConjecture.Surgery.Terminal.Gluing
