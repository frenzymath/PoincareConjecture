import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Relative.HalfSpace



noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]



theorem exists_supported_correction_of_halfspace_agreement
    (l : E →L[Real] Real) (v : E) (hlv : l v = 1) (c : Real)
    (H H' : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hheight : ∀ x, l (H x) = l x)
    (hagree : EqOn H' H {x | c ≤ l x}) {C : Set E} (hC : IsCompact C) :
    ∃ K : Set E, IsCompact K ∧
      ∃ G : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x ∉ K, G x = x) ∧ EqOn G id {x | c ≤ l x} ∧
        (∀ x ∈ C, G (H x) = H' x) ∧ G '' (H '' C) = H' '' C := by
  let F := H.symm.trans H'
  have hF : EqOn F id {x | c ≤ l x} := by
    intro x hx
    have hh := hheight (H.symm x)
    rw [H.apply_symm_apply] at hh
    change H' (H.symm x) = x
    rw [hagree (by change c ≤ l (H.symm x); rw [← hh]; exact hx),
      H.apply_symm_apply]
  obtain ⟨K, hK, G, hfix, hhalf, heq⟩ :=
    exists_supported_agreement_of_fixed_halfspace l v hlv c F hF (hC.image H.continuous)
  have hpoint (x : E) (hx : x ∈ C) : G (H x) = H' x := by
    rw [heq (mem_image_of_mem H hx)]
    change H' (H.symm (H x)) = H' x
    rw [H.symm_apply_apply]
  refine ⟨K, hK, G, hfix, hhalf, hpoint, ?_⟩
  rw [image_image]
  exact image_congr hpoint



theorem exists_supported_correction_of_halfspace_agreement_preserving_linear
    (l : E →L[Real] Real) (v : E) (hlv : l v = 1) (c : Real)
    (H H' : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hheight : ∀ x, l (H x) = l x) (hheight' : ∀ x, l (H' x) = l x)
    (hagree : EqOn H' H {x | c ≤ l x}) {C : Set E} (hC : IsCompact C) :
    ∃ K : Set E, IsCompact K ∧
      ∃ G : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x ∉ K, G x = x) ∧ EqOn G id {x | c ≤ l x} ∧
        (∀ x, l (G x) = l x) ∧
        (∀ x ∈ C, G (H x) = H' x) ∧ G '' (H '' C) = H' '' C := by
  let F := H.symm.trans H'
  have hF : EqOn F id {x | c ≤ l x} := by
    intro x hx
    have hh := hheight (H.symm x)
    rw [H.apply_symm_apply] at hh
    change H' (H.symm x) = x
    rw [hagree (by change c ≤ l (H.symm x); rw [← hh]; exact hx),
      H.apply_symm_apply]
  have hlinear (x : E) : l (F x) = l x := by
    change l (H' (H.symm x)) = l x
    rw [hheight', ← hheight (H.symm x), H.apply_symm_apply]
  obtain ⟨K, hK, G, hfix, hhalf, hlevel, heq⟩ :=
    exists_supported_agreement_of_fixed_halfspace_preserving_linear
      l v hlv c F hF (hC.image H.continuous) l hlinear
  have hpoint (x : E) (hx : x ∈ C) : G (H x) = H' x := by
    rw [heq (mem_image_of_mem H hx)]
    change H' (H.symm (H x)) = H' x
    rw [H.symm_apply_apply]
  refine ⟨K, hK, G, hfix, hhalf, hlevel, hpoint, ?_⟩
  rw [image_image]
  exact image_congr hpoint

end Poincare.Manifold.Schoenflies
