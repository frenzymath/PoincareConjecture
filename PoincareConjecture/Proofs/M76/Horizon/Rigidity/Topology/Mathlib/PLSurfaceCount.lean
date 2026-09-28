import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceTriangulationCount
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem FinitePiecewiseAffineOn.surfaceEulerCount_eq_of_injOn
    {f : E → F} {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
    (hf : FinitePiecewiseAffineOn f K.space)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hdimK : ∀ s ∈ K.faces, s.card ≤ 3) (hdimL : ∀ s ∈ L.faces, s.card ≤ 3)
    (hinj : InjOn f K.space) (himage : f '' K.space = L.space) :
    K.surfaceEulerCount = L.surfaceEulerCount := by
  classical
  obtain ⟨J, hJ, hJs, hfJ⟩ := hf
  let : Finite J.faces := hJ.to_subtype
  have hcover : ∀ x ∈ K.space, ∃ s : J.faces,
      x ∈ convexHull ℝ (s.val : Set E) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp (hJs.symm ▸ hx)
    exact ⟨⟨s, hs⟩, hxs⟩
  obtain ⟨R, hR, hRK, hdimR, href⟩ := K.exists_subdivision_refines_finite_cover
    hK (N := 2) hdimK ((↑) : J.faces → Finset E) (fun s => J.indep s.property) hcover
  have hfR : R.AffineOnFaces f := hfJ.of_face_containment (by
    intro s hs
    obtain ⟨t, ht⟩ := href s hs
    exact ⟨t.val, t.property, ht⟩)
  have hinjR : InjOn f R.space := hRK.space_eq ▸ hinj
  let Q := hfR.embeddedImage hinjR
  have hQ : Q.faces.Finite := hfR.embeddedImage_finite hinjR hR
  have hdimQ : ∀ s ∈ Q.faces, s.card ≤ 3 := by
    intro s hs
    rw [show Q.faces = _ from hfR.embeddedImage_faces hinjR] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans (hdimR t ht)
  have hQs : Q.space = L.space := by
    rw [show Q.space = _ from hfR.embeddedImage_space hinjR, hRK.space_eq, himage]
  exact (K.surfaceEulerCount_eq_of_space_eq R hK hR hdimK hdimR hRK.space_eq.symm).trans
    ((hfR.surfaceEulerCount_embeddedImage hinjR).symm.trans
      (Q.surfaceEulerCount_eq_of_space_eq L hQ hL hdimQ hdimL hQs))

end Geometry
