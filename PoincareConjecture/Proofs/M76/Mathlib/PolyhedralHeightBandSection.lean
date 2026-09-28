import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_heightBand_section_chart (K : SimplicialComplex ℝ (E × ℝ))
    (hK : K.faces.Finite) {B : Set E} {lower upper : E → ℝ}
    (hspace : K.space = {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)})
    (c : ℝ) :
    ∃ H : {x : E | x ∈ B ∧ c ∈ Icc (lower x) (upper x)} ≃ₜ
        (K.space ∩ {p : E × ℝ | p.2 = c} : Set (E × ℝ)),
      H.IsFinitePL ∧ ∀ x, (H x : E × ℝ) = ((x : E), c) := by
  let A : (E × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ E ℝ).toAffineMap
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_affineLevel_complex hK A c
  have hproj : FinitePiecewiseAffineOn (Prod.fst : E × ℝ → E) J.space :=
    ⟨J, hJ, rfl, J.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap⟩
  have hinj : InjOn (Prod.fst : E × ℝ → E) J.space := by
    intro p hp q hq hpq
    have hp' : p ∈ K.space ∩ {p : E × ℝ | p.2 = c} := hJs ▸ hp
    have hq' : q ∈ K.space ∩ {p : E × ℝ | p.2 = c} := hJs ▸ hq
    exact Prod.ext hpq (hp'.2.trans hq'.2.symm)
  have himage : Prod.fst '' J.space = {x : E | x ∈ B ∧ c ∈ Icc (lower x) (upper x)} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hp' : p ∈ K.space ∩ {p : E × ℝ | p.2 = c} := hJs ▸ hp
      have hpB : p ∈ {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} :=
        hspace ▸ hp'.1
      exact ⟨hpB.1, hp'.2 ▸ hpB.2⟩
    · intro hx
      refine ⟨(x, c), ?_, rfl⟩
      rw [hJs, hspace]
      exact ⟨hx, rfl⟩
  obtain ⟨e, he, heval⟩ := hproj.exists_homeomorph_image hinj
  let H := (Homeomorph.setCongr himage.symm).trans
    (e.symm.trans (Homeomorph.setCongr hJs))
  refine ⟨H, he.symm.setCongr himage hJs, fun x => ?_⟩
  apply Prod.ext
  · change ((e.symm ⟨x, himage.symm ▸ x.property⟩ : E × ℝ).1) = (x : E)
    have h := heval (e.symm ⟨x, himage.symm ▸ x.property⟩)
    simpa only [e.apply_symm_apply] using h.symm
  · exact (H x).property.2

end Geometry.SimplicialComplex
