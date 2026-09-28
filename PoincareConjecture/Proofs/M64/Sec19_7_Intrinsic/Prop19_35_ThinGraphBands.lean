import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SeparatedArcStrips
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_thin_graph_bands
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hf : ContDiffOn ℝ ∞ f X)
    {a b ua wa ub wb : ℝ} (hab : a < b) (hI : Icc a b ⊆ X)
    (P : TransverseGraphCuts f a b ua wa ub wb)
    {delta : ℝ} (hdelta : 0 < delta) :
    let C := (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
    ∃ epsilon > 0, ∀ ra ∈ Ioo (0 : ℝ) epsilon, ∀ rb ∈ Ioo (0 : ℝ) epsilon,
      ∃ B : ObliqueBandFaces C f a b ua wa ub wb ra rb,
        B.cuts.left = P.left ∧ B.cuts.right = P.right ∧
        (∀ q, B.coordinates q = P.linearCoordinates L hX hf (collarParameterEquiv q)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, B.height t < delta) ∧
        B.carrier = P.linearCoordinates L hX hf ''
          {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ B.height q.1} ∧
        B.leftCut = segment ℝ (L (a, f a)) (L (a, f a) + ra • L (ua, wa)) ∧
        B.rightCut = segment ℝ (L (b, f b)) (L (b, f b) + rb • L (ub, wb)) := by
  let C := (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    contMDiffOn_iff_contDiffOn.mpr (collarParameterEquiv.trans L).contDiff.contDiffOn
  have hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    contMDiffOn_iff_contDiffOn.mpr (collarParameterEquiv.trans L).symm.contDiff.contDiffOn
  let radius := min P.radius delta
  have hradius : 0 < radius := lt_min P.radius_pos hdelta
  have hrP : radius ≤ P.radius := min_le_left _ _
  let Q : TransverseGraphCuts f a b ua wa ub wb := {
    left := P.left
    right := P.right
    radius := radius
    radius_pos := hradius
    height_subset := fun _ hz => P.height_subset ⟨by linarith [hz.1], hz.2.trans_le hrP⟩
    separated := fun z hz => P.separated z ⟨by linarith [hz.1], hz.2.trans_le hrP⟩ }
  obtain ⟨epsilon, hepsilon, hinterface⟩ := exists_obliquePolygonalBoundary Q hab hX hf hI
  refine ⟨epsilon, hepsilon, ?_⟩
  intro ra hra rb hrb
  obtain ⟨I⟩ := hinterface ra hra rb hrb
  let B := obliqueBandFacesOfInterface C hC hCi hX hf hI Q hra.1 hrb.1 I
    (by intro x hx z hz hzr; exact mem_univ _) (0 : AnnulusCoordinates)
    (by intro x hx; simp)
  have hcoordinates (q : AnnulusCoordinates) :
      B.coordinates q = P.linearCoordinates L hX hf (collarParameterEquiv q) := by
    change C (collarParameterEquiv.symm (Q.coordinates hX hf (collarParameterEquiv q))) = _
    change L (collarParameterEquiv
      (collarParameterEquiv.symm (Q.coordinates hX hf (collarParameterEquiv q)))) = _
    rw [collarParameterEquiv.apply_symm_apply, P.linearCoordinates_apply,
      Q.coordinates_apply, P.coordinates_apply]
  refine ⟨B, rfl, rfl, hcoordinates, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [← B.cut_interval_cover] at ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    rw [B.height_eq_upperGraph hi]
    exact ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).upperGraph_bounds
      hi).2.trans_le (min_le_right P.radius delta)
  · rw [B.carrier_eq_image, B.band_eq_subgraph]
    ext p
    constructor
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, hq, (hcoordinates q).symm.trans heq⟩
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q, ?_, ?_⟩
      · simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using hq
      · rw [hcoordinates, collarParameterEquiv.apply_symm_apply]
        exact heq
  · change (fun q : ℝ × ℝ => L (collarParameterEquiv (collarParameterEquiv.symm q))) ''
        segment ℝ (a, f a) (a + ra * ua, f a + ra * wa) = _
    simp only [collarParameterEquiv.apply_symm_apply]
    change L.toLinearMap.toAffineMap '' segment ℝ (a, f a)
      (a + ra * ua, f a + ra * wa) = _
    rw [image_segment ℝ L.toLinearMap.toAffineMap]
    congr 1
    rw [← map_smul, ← map_add]
    rfl
  · change (fun q : ℝ × ℝ => L (collarParameterEquiv (collarParameterEquiv.symm q))) ''
        segment ℝ (b, f b) (b + rb * ub, f b + rb * wb) = _
    simp only [collarParameterEquiv.apply_symm_apply]
    change L.toLinearMap.toAffineMap '' segment ℝ (b, f b)
      (b + rb * ub, f b + rb * wb) = _
    rw [image_segment ℝ L.toLinearMap.toAffineMap]
    congr 1
    rw [← map_smul, ← map_add]
    rfl

end PoincareConjecture
