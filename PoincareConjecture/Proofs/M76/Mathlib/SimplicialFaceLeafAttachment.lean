import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicCellLeafAttachment
import PoincareConjecture.Proofs.M76.Mathlib.NormalizedTransverseTarget
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFaceTransversality









set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem IsSmoothLeafFieldOn.exists_simplicialFaceAttachment
    {P : E → EuclideanSubspace E} {U B : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hB : IsClosed B) (hBU : B ⊆ U)
    (K : SimplicialComplex ℝ E) {s t : Finset E} (hs : s ∈ K.faces)
    (ht : t ∈ K.faces) (hst : s ⊆ t) (m : ℕ) (hcard : t.card = m + 1)
    (hboundary : intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ⊆ U)
    (hBS : B ∩ convexHull ℝ (s : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdim : ∀ x ∈ U, Module.finrank ℝ (P x).subspace + m = Module.finrank ℝ E)
    [ContractibleSpace (SecantTransversePlaneSpace m (K.closedFaceStar s).space)]
    (htrans : ∀ x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)),
      (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space) :
    ∃ W : Set E, IsOpen W ∧ B ∪ convexHull ℝ (s : Set E) ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ y ∈ W, Module.finrank ℝ (R y).subspace + m = Module.finrank ℝ E) ∧
        R =ᶠ[𝓝ˢ B] P ∧ ∀ x ∈ convexHull ℝ (s : Set E),
          (R x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  let T := (affineSpan ℝ (t : Set E)).direction
  have hTdim : Module.finrank ℝ T = m := K.finrank_faceDirection_of_card ht hcard
  have htstar : t ∈ (K.closedFaceStar s).faces :=
    ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩
  have hdisjoint : ∀ L : Submodule ℝ E,
      L.IsSecantTransverse (K.closedFaceStar s).space → Disjoint T L :=
    fun _ hL => (K.closedFaceStar s).disjoint_faceDirection_of_isSecantTransverse htstar hL
  let : ContractibleSpace
      (SecantTransversePlaneSpace (Module.finrank ℝ T) (K.closedFaceStar s).space) :=
    hTdim.symm ▸ inferInstance
  let := T.subtypeL.contractible_frameTransverseSpace_of_planes Subtype.val_injective
    (K.closedFaceStar s).space (by
      change ∀ L : Submodule ℝ E,
        L.IsSecantTransverse (K.closedFaceStar s).space → Disjoint T.subtype.range L
      simpa only [Submodule.range_subtype] using hdisjoint)
  have hT : (affineSpan ℝ (convexHull ℝ (s : Set E))).direction ≤ T := by
    rw [affineSpan_convexHull]
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hst)
  have h := hP.exists_intrinsicCellAttachment hU hB hBU (s.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
    hboundary hBS T hT (by simpa only [hTdim] using hdim)
    (K.closedFaceStar s).space hdisjoint htrans
  simpa only [hTdim] using h

end Geometry.EuclideanSubspace
