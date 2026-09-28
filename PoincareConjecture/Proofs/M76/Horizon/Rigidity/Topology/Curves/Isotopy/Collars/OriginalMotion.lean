import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

theorem exists_original_collar_motion
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {eps : ℝ} (heps : 0 < eps)
    (c : E × ℝ → X)
    (hcPL : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) eps))
    (hemb : IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) eps) => c z))
    (H : I → K.space ≃ₜ K.space)
    (hc : Continuous (fun z : I × K.space => H z.1 z.2))
    (hci : Continuous (fun z : I × K.space => (H z.1).symm z.2))
    (hzero : ∀ x, H 0 x = x)
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ K.space))
    (hvalue : ∀ t : I, ∀ x : K.space, track ((t : ℝ), x) = (H t x : E)) :
    let P := K.space ×ˢ Icc (0 : ℝ) eps
    let D := c '' P
    ∃ (C : P ≃ₜ D) (Q : I → D ≃ₜ D),
      (∀ z : P, (C z : X) = c z) ∧ IsCompact D ∧ IsClosed D ∧
      Continuous (fun z : I × D => Q z.1 z.2) ∧
      Continuous (fun z : I × D => (Q z.1).symm z.2) ∧
      Q 0 = Homeomorph.refl D ∧
      (∀ t : I, ∀ z : P, Q t (C z) = C (scaledCollarExtension heps H hc hci t z)) ∧
      (∀ t : I, ∀ x : K.space,
        (Q t (C ⟨(x, 0), x.property, le_rfl, heps.le⟩) : X) = c (H t x, 0)) ∧
      (∀ t : I, ∀ x : K.space,
        Q t (C ⟨(x, eps), x.property, heps.le, le_rfl⟩) =
          C ⟨(x, eps), x.property, heps.le, le_rfl⟩) ∧
      ∀ t : I,
        (∃ g : E × ℝ → X, PolyhedralPLInCharts e g P ∧
          ∀ z : P, g z = (Q t (C z) : X)) ∧
        (∃ g : E × ℝ → X, PolyhedralPLInCharts e g P ∧
          ∀ z : P, g z = ((Q t).symm (C z) : X)) := by
  let P := K.space ×ˢ Icc (0 : ℝ) eps
  let D := c '' P
  have hrange : range (fun z : P => c z) = D := by
    ext x
    simp only [mem_range, D, mem_image, Subtype.exists, exists_prop]
  obtain ⟨C, hCv⟩ : ∃ C : P ≃ₜ D, ∀ z : P, (C z : X) = c z :=
    ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hrange), fun _ => rfl⟩
  let M (t : I) := scaledCollarExtension heps H hc hci t
  let Q (t : I) := C.symm.trans ((M t).trans C)
  have hQ (t : I) (z : P) : Q t (C z) = C (M t z) := by
    change C (M t (C.symm (C z))) = _
    rw [C.symm_apply_apply]
  have hcompact : IsCompact D :=
    ((K.isCompact_space_of_finite hK).prod isCompact_Icc).image_of_continuousOn hcPL.continuousOn
  have htransport (m : P ≃ₜ P) (hm : m.IsFinitePL) :
      ∃ g : E × ℝ → X, PolyhedralPLInCharts e g P ∧
        ∀ z : P, g z = (C (m z) : X) := by
    obtain ⟨f, hf, hfv⟩ := hm
    have hmaps : MapsTo f P P := by
      intro z hz
      rw [← hfv ⟨z, hz⟩]
      exact (m ⟨z, hz⟩).property
    have hfcopy := hf
    obtain ⟨J, hJ, hJs, _⟩ := hfcopy
    have hg := hcPL.comp_finitePiecewiseAffineOn J hJ
      (hJs.symm ▸ hf) (hJs.symm ▸ hmaps)
    refine ⟨c ∘ f, hJs ▸ hg, ?_⟩
    intro z
    change c (f z) = _
    rw [← hfv z]
    exact (hCv (m z)).symm
  refine ⟨C, Q, hCv, hcompact, hcompact.isClosed, ?_, ?_, ?_, hQ, ?_, ?_, ?_⟩
  · change Continuous (fun z : I × D => C (M z.1 (C.symm z.2)))
    have hin : Continuous (fun z : I × D => (z.1, C.symm z.2)) :=
      continuous_fst.prodMk (C.symm.continuous.comp continuous_snd)
    have hM : Continuous (fun z : I × P => M z.1 z.2) :=
      continuous_scaledCollarExtension heps H hc hci
    exact C.continuous.comp (f := fun z : I × D => M z.1 (C.symm z.2))
      (hM.comp (f := fun z : I × D => (z.1, C.symm z.2)) hin)
  · change Continuous (fun z : I × D => C ((M z.1).symm (C.symm z.2)))
    have hin : Continuous (fun z : I × D => (z.1, C.symm z.2)) :=
      continuous_fst.prodMk (C.symm.continuous.comp continuous_snd)
    have hM : Continuous (fun z : I × P => (M z.1).symm z.2) :=
      continuous_scaledCollarExtension_symm heps H hc hci
    exact C.continuous.comp (f := fun z : I × D => (M z.1).symm (C.symm z.2))
      (hM.comp (f := fun z : I × D => (z.1, C.symm z.2)) hin)
  · apply Homeomorph.ext
    intro y
    obtain ⟨z, rfl⟩ := C.surjective y
    rw [hQ]
    change C (scaledCollarExtension heps H hc hci 0 z) = C z
    rw [scaledCollarExtension_zero heps H hc hci hzero]
    rfl
  · intro t x
    rw [hQ, scaledCollarExtension_outer]
    exact hCv _
  · intro t x
    rw [hQ, scaledCollarExtension_inner heps H hc hci hzero]
  · intro t
    have hm := isFinitePL_scaledCollarExtension heps H hc hci track htrack hvalue t
    obtain ⟨g, hg, hgv⟩ := htransport (M t) hm
    obtain ⟨g', hg', hgv'⟩ := htransport (M t).symm hm.symm
    refine ⟨⟨g, hg, fun z => (hgv z).trans (congrArg Subtype.val (hQ t z)).symm⟩,
      g', hg', ?_⟩
    intro z
    change g' z = (C ((M t).symm (C.symm (C z))) : X)
    rw [C.symm_apply_apply]
    exact hgv' z

end PoincareConjecture.M76.CollarIsotopy
