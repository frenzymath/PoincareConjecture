import PoincareConjecture.Proofs.M76.Mathlib.ConvexCellLeafAttachment
import PoincareConjecture.Proofs.M76.Mathlib.NestedDirectionCoordinates









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsSmoothLeafFieldOn.exists_intrinsicCellAttachment
    {P : E → EuclideanSubspace E} {U B S : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hB : IsClosed B) (hBU : B ⊆ U)
    (hS : IsCompact S) (hc : Convex ℝ S) (hne : S.Nonempty)
    (hboundary : intrinsicFrontier ℝ S ⊆ U)
    (hBS : B ∩ S ⊆ intrinsicFrontier ℝ S)
    (T : Submodule ℝ E) (hT : (affineSpan ℝ S).direction ≤ T)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ T = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint T L)
    [ContractibleSpace {Q : E →L[ℝ] T // Function.RightInverse T.subtypeL Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ x ∈ intrinsicFrontier ℝ S, (P x).subspace.IsSecantTransverse A) :
    ∃ W : Set E, IsOpen W ∧ B ∪ S ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ y ∈ W, Module.finrank ℝ (R y).subspace + Module.finrank ℝ T = Module.finrank ℝ E) ∧
        R =ᶠ[𝓝ˢ B] P ∧ ∀ x ∈ S, (R x).subspace.IsSecantTransverse A := by
  obtain ⟨p, hp⟩ := hne
  let pA : affineSpan ℝ S := ⟨p, subset_affineSpan ℝ S hp⟩
  let c := (affineSpan ℝ S).directionCoordinates pA
  let C := c ⁻¹' S
  obtain ⟨hC, hCc, hCi, himage, hfront⟩ :=
    AffineSubspace.convexBody_directionCoordinates hS hc pA
  let a := T.affineSlice p
  let b := (affineSpan ℝ S).direction.nestedDirectionCoordinates T hT
  have ha : a.contLinear = T.subtypeL := T.affineSlice_contLinear p
  have hzero : (fun x => a (b (x, 0))) = c := by
    funext x
    exact Submodule.affineSlice_nestedDirectionCoordinates (affineSpan ℝ S) T hT pA x
  let : ContractibleSpace {Q : E →L[ℝ] T // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A} := by rw [ha]; infer_instance
  have hJ : Function.Injective a.contLinear := by rw [ha]; exact Subtype.val_injective
  have hboundary' : (fun x => a (b (x, 0))) '' frontier C ⊆ U := by
    rw [hzero]
    exact hfront ▸ hboundary
  have hBS' : B ∩ (fun x => a (b (x, 0))) '' C ⊆
      (fun x => a (b (x, 0))) '' frontier C := by
    rw [hzero, himage, hfront]
    exact hBS
  obtain ⟨W, hW, hcover, R, hR, hRdim, hRP, hRT⟩ :=
    hP.exists_convexCellAttachment hU hB hBU a b hJ hC hCc hCi hboundary' hBS'
      hdim A (by
        rw [ha]
        change ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint T.subtype.range L
        simpa only [Submodule.range_subtype] using hdisjoint)
      (fun x hx => htrans _ (hfront ▸ (hzero ▸ mem_image_of_mem c hx)))
  refine ⟨W, hW, ?_, R, hR, hRdim, hRP, ?_⟩
  · rwa [hzero, himage] at hcover
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := himage ▸ hx
    change (R (c y)).subspace.IsSecantTransverse A
    rw [← congrFun hzero y]
    exact hRT y hy

end Geometry.EuclideanSubspace
