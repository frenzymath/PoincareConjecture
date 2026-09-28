import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.TranslationTrack



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76
local notation "I" => unitInterval

theorem exists_finitePL_conjugate_track
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F} (hL : L.faces.Finite)
    (B : K.space ≃ₜ L.space) (hB : B.IsFinitePL)
    (G : I → K.space ≃ₜ K.space)
    (hG : Continuous (fun z : I × K.space => G z.1 z.2))
    (hGi : Continuous (fun z : I × K.space => (G z.1).symm z.2))
    (hG0 : G 0 = Homeomorph.refl K.space)
    (track : ℝ × E → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ K.space))
    (hvalue : ∀ t : I, ∀ x : K.space, track ((t : ℝ), x) = (G t x : E)) :
    ∃ (H : I → L.space ≃ₜ L.space) (newTrack : ℝ × F → F),
      Continuous (fun z : I × L.space => H z.1 z.2) ∧
      Continuous (fun z : I × L.space => (H z.1).symm z.2) ∧
      H 0 = Homeomorph.refl L.space ∧
      FinitePiecewiseAffineOn newTrack (Icc (0 : ℝ) 1 ×ˢ L.space) ∧
      (∀ t : I, ∀ x : L.space, newTrack ((t : ℝ), x) = (H t x : F)) ∧
      ∀ t : I, ∀ x : K.space, H t (B x) = B (G t x) := by
  let H (t : I) : L.space ≃ₜ L.space := (B.symm.trans (G t)).trans B
  have hH : Continuous (fun z : I × L.space => H z.1 z.2) :=
    B.continuous.comp (hG.comp (continuous_fst.prodMk (B.symm.continuous.comp continuous_snd)))
  have hHi : Continuous (fun z : I × L.space => (H z.1).symm z.2) :=
    B.continuous.comp (hGi.comp (continuous_fst.prodMk (B.symm.continuous.comp continuous_snd)))
  have hH0 : H 0 = Homeomorph.refl L.space := by
    apply Homeomorph.ext
    intro x
    change B (G 0 (B.symm x)) = x
    rw [hG0]
    exact B.apply_symm_apply x
  obtain ⟨r, hr, hrval⟩ := hB.symm
  obtain ⟨q, hq, hqval⟩ := hB
  obtain ⟨J, hJ, hJs⟩ := exists_finite_interval_cylinder L hL
    (show (0 : ℝ) < 1 by norm_num)
  have hfst : FinitePiecewiseAffineOn (fun z : ℝ × F => z.1) J.space :=
    (J.affineOnFaces_affine (ContinuousLinearMap.fst ℝ ℝ F).toContinuousAffineMap).finitePiecewiseAffineOn hJ
  have hsnd : FinitePiecewiseAffineOn (fun z : ℝ × F => z.2) J.space :=
    (J.affineOnFaces_affine (ContinuousLinearMap.snd ℝ ℝ F).toContinuousAffineMap).finitePiecewiseAffineOn hJ
  have hrin : FinitePiecewiseAffineOn (fun z : ℝ × F => r z.2) J.space :=
    hr.comp hsnd (fun z hz => (hJs.subset hz).2)
  have hparameter := hfst.prod_mk hrin
  have hmaps : MapsTo (fun z : ℝ × F => (z.1, r z.2)) J.space
      (Icc (0 : ℝ) 1 ×ˢ K.space) := by
    intro z hz
    have hzL := (hJs.subset hz).2
    refine ⟨(hJs.subset hz).1, ?_⟩
    change r z.2 ∈ K.space
    rw [← hrval ⟨z.2, hzL⟩]
    exact (B.symm ⟨z.2, hzL⟩).property
  have hmoved : FinitePiecewiseAffineOn (fun z : ℝ × F => track (z.1, r z.2)) J.space :=
    htrack.comp hparameter hmaps
  have hmovedK : MapsTo (fun z : ℝ × F => track (z.1, r z.2)) J.space K.space := by
    intro z hz
    have hz' := hJs.subset hz
    change track (z.1, r z.2) ∈ K.space
    rw [← hrval ⟨z.2, hz'.2⟩, hvalue ⟨z.1, hz'.1⟩]
    exact (G ⟨z.1, hz'.1⟩ (B.symm ⟨z.2, hz'.2⟩)).property
  refine ⟨H, (fun z => q (track (z.1, r z.2))), hH, hHi, hH0,
    hJs ▸ hq.comp hmoved hmovedK, ?_, ?_⟩
  · intro t x
    change q (track ((t : ℝ), r x)) = (H t x : F)
    rw [← hrval x, hvalue t, ← hqval]
    rfl
  · intro t x
    change B (G t (B.symm (B x))) = B (G t x)
    rw [B.symm_apply_apply]

end PoincareConjecture.M76
