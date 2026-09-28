import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import Mathlib.Topology.OpenPartialHomeomorph.Constructions








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

theorem exists_global_chart_of_open_parametrization
    {Y E ι : Type*} [TopologicalSpace Y] [Nonempty Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} (hQ : IsOpen Q) (J : Q ≃ₜ Y)
    (q : ι → OpenPartialHomeomorph Y E) (f : ι → E → E)
    (hf : ∀ i (z : Q), f i z = q i (J z))
    (hPL : ∀ i, LocallyPiecewiseAffineOn (f i)
      ((Subtype.val : Q → E) '' (J ⁻¹' (q i).source))) :
    ∃ b : OpenPartialHomeomorph Y E,
      b.source = univ ∧ b.target = Q ∧ (∀ z : Q, b (J z) = z) ∧
      (∀ i, IsOpen ((Subtype.val : Q → E) '' (J ⁻¹' (q i).source))) ∧
      ∀ i, (q i).symm.trans b ∈ piecewiseAffineGroupoid E := by
  classical
  have hQne : Nonempty Q := ⟨J.symm (Classical.choice inferInstance)⟩
  let inclusion := (⟨Q, hQ⟩ : TopologicalSpace.Opens E).openPartialHomeomorphSubtypeCoe hQne
  let b : OpenPartialHomeomorph Y E := J.symm.toOpenPartialHomeomorph.trans inclusion
  have hsource : b.source = univ := by
    simp [b, inclusion]
  have htarget : b.target = Q := by
    simp [b, inclusion]
  have hvalue (z : Q) : b (J z) = z := by
    change (J.symm (J z) : E) = z
    rw [J.symm_apply_apply]
  have hinverse (z : Q) : b.symm z = J z := by
    rw [← hvalue z]
    exact b.left_inv (hsource.symm ▸ mem_univ _)
  have hdomain (i : ι) : (b.symm.trans (q i)).source =
      (Subtype.val : Q → E) '' (J ⁻¹' (q i).source) := by
    ext z
    constructor
    · intro hz
      have hzQ : z ∈ Q := htarget ▸ hz.1
      refine ⟨⟨z, hzQ⟩, ?_, rfl⟩
      change J ⟨z, hzQ⟩ ∈ (q i).source
      rw [← hinverse]
      exact hz.2
    · rintro ⟨z, hz, rfl⟩
      refine ⟨htarget.symm ▸ z.property, ?_⟩
      change b.symm z ∈ (q i).source
      rw [hinverse]
      exact hz
  refine ⟨b, hsource, htarget, hvalue, ?_, ?_⟩
  · intro i
    rw [← hdomain]
    exact (b.symm.trans (q i)).open_source
  · intro i
    have hforward : b.symm.trans (q i) ∈ piecewiseAffineGroupoid E := by
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      rw [hdomain]
      apply (hPL i).congr
      rintro z ⟨u, hu, rfl⟩
      change f i u = q i (b.symm u)
      rw [hinverse]
      exact hf i u
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid E).symm hforward

end PoincareConjecture.M76.Dehn.Annuli.RimBands
