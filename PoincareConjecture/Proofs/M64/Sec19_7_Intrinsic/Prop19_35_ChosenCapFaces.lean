import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FittedCornerCap












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Triangles

namespace PoincareConjecture




theorem m64Intrinsic_exists_face_of_chosen_cap
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 < r)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hF : ContDiffOn ℝ ∞ F F.source) (hFi : ContDiffOn ℝ ∞ F.symm F.target) :
    ∃ face : SmoothFace AnnulusCoordinates,
      face.map = F ∘ collarParameterEquiv ∧
      face.source = convexHull ℝ (range (rightTriangleBasis hr)) ∧
      face.carrier = F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ∧
      InjOn face.map face.source ∧
      (∀ t : ℝ, (face.boundary 0).map t = F ((1 - t) * r, t * r)) ∧
      (∀ t : ℝ, (face.boundary 1).map t = F (0, t * r)) ∧
      (∀ t : ℝ, (face.boundary 2).map t = F (t * r, 0)) := by
  let C := collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans F
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    contMDiffOn_iff_contDiffOn.mpr
      (hF.comp collarParameterEquiv.contDiff.contDiffOn (fun _ hz => hz.2))
  have hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    contMDiffOn_iff_contDiffOn.mpr
      (collarParameterEquiv.symm.contDiff.comp_contDiffOn (hFi.mono (fun _ hz => hz.1)))
  have htriangle : convexHull ℝ (range (rightTriangleBasis hr)) ⊆ C.source := by
    intro z hz
    exact ⟨mem_univ _, hsource ((mem_rightTriangleBasis_convexHull hr z).mp hz)⟩
  obtain ⟨face, hmap, hfaceSource, hcarrier, hinj, hboundary⟩ :=
    exists_smoothFace_of_smooth_coordinates C hC hCi (rightTriangleBasis hr) htriangle
      (0 : AnnulusCoordinates) (by intro z _; simp)
  refine ⟨face, hmap, hfaceSource, ?_, hinj, ?_, ?_, ?_⟩
  · rw [hcarrier]
    ext z
    constructor
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, (mem_rightTriangleBasis_convexHull hr q).mp hq, heq⟩
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q,
        (mem_rightTriangleBasis_convexHull hr _).mpr hq, ?_⟩
      change F (collarParameterEquiv (collarParameterEquiv.symm q)) = z
      rwa [collarParameterEquiv.apply_symm_apply]
  · intro t
    rw [hboundary]
    simp only [C, Function.comp_apply, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    simp [affineChartSegment, rightTriangleBasis_apply, collarParameterEquiv, mul_comm]
    congr 1
    ring
  · intro t
    rw [hboundary]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]
  · intro t
    rw [hboundary]
    rw [show Fin.succAbove (2 : Fin 3) 1 = 1 by decide]
    simp [C, Function.comp_apply, affineChartSegment, rightTriangleBasis_apply,
      collarParameterEquiv, mul_comm]

end PoincareConjecture
