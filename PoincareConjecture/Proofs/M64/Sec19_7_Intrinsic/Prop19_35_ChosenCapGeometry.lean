import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapFaces
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReflexCornerFrontier












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Triangles

namespace PoincareConjecture




theorem m64Intrinsic_chosen_cap_coordinate_data
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 < r)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (face : SmoothFace AnnulusCoordinates)
    (hcarrier : face.carrier =
      F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r})
    (hzero : ∀ t : ℝ, (face.boundary 0).map t = F ((1 - t) * r, t * r))
    (hone : ∀ t : ℝ, (face.boundary 1).map t = F (0, t * r))
    (htwo : ∀ t : ℝ, (face.boundary 2).map t = F (t * r, 0)) :
    let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
    convexHull ℝ (range (rightTriangleBasis hr)) ⊆ C.source ∧
    face.carrier = C '' convexHull ℝ (range (rightTriangleBasis hr)) ∧
    ∀ k : Fin 3, (face.boundary k).map = C ∘
      affineChartSegment (rightTriangleBasis hr (k.succAbove 0))
        (rightTriangleBasis hr (k.succAbove 1)) := by
  dsimp only
  let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ⟨mem_univ _, hsource ((mem_rightTriangleBasis_convexHull hr z).mp hz)⟩
  · rw [hcarrier]
    ext z
    constructor
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q,
        (mem_rightTriangleBasis_convexHull hr _).mpr hq, ?_⟩
      change F (collarParameterEquiv (collarParameterEquiv.symm q)) = z
      rwa [collarParameterEquiv.apply_symm_apply]
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, (mem_rightTriangleBasis_convexHull hr q).mp hq, heq⟩
  · intro k
    change (face.boundary k).map = C ∘ _
    fin_cases k
    · funext t
      change (face.boundary 0).map t =
        C (affineChartSegment (rightTriangleBasis hr 1) (rightTriangleBasis hr 2) t)
      rw [hzero]
      simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
        collarParameterEquiv, mul_comm]
      congr 1
      ring
    · funext t
      change (face.boundary 1).map t =
        C (affineChartSegment (rightTriangleBasis hr 0) (rightTriangleBasis hr 2) t)
      rw [hone]
      simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
        collarParameterEquiv, mul_comm]
    · funext t
      change (face.boundary 2).map t =
        C (affineChartSegment (rightTriangleBasis hr 0) (rightTriangleBasis hr 1) t)
      rw [htwo]
      simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
        collarParameterEquiv, mul_comm]





theorem m64Intrinsic_exists_coordinate_face_of_chosen_cap
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 < r)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hF : ContDiffOn ℝ ∞ F F.source) (hFi : ContDiffOn ℝ ∞ F.symm F.target) :
    ∃ face : SmoothFace AnnulusCoordinates,
      face.carrier = F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ∧
      (∀ t : ℝ, (face.boundary 0).map t = F ((1 - t) * r, t * r)) ∧
      (∀ t : ℝ, (face.boundary 1).map t = F (0, t * r)) ∧
      (∀ t : ℝ, (face.boundary 2).map t = F (t * r, 0)) ∧
      ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
        (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        convexHull ℝ (range b) ⊆ C.source ∧
        face.carrier = C '' convexHull ℝ (range b) ∧
        ∀ k : Fin 3, (face.boundary k).map = C ∘
          affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) := by
  obtain ⟨face, _, _, hc, _, hzero, hone, htwo⟩ :=
    m64Intrinsic_exists_face_of_chosen_cap F hr hsource hF hFi
  let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
  refine ⟨face, hc, hzero, hone, htwo, C, rightTriangleBasis hr, ?_, ?_,
    m64Intrinsic_chosen_cap_coordinate_data F hr hsource face hc hzero hone htwo⟩
  · exact contMDiffOn_iff_contDiffOn.mpr
      (hF.comp collarParameterEquiv.contDiff.contDiffOn (fun _ hz => hz.2))
  · exact contMDiffOn_iff_contDiffOn.mpr
      (collarParameterEquiv.symm.contDiff.comp_contDiffOn (hFi.mono (fun _ hz => hz.1)))

end PoincareConjecture
