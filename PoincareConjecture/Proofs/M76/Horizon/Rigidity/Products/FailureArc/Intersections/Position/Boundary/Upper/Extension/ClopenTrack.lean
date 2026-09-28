import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.ClopenMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.Tracks



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "I" => unitInterval


theorem exists_finitePL_clopen_track_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K L : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hLK : L.space ⊆ K.space)
    (hclopen : IsClopen ((Subtype.val : K.space → E) ⁻¹' L.space))
    (G : I → L.space ≃ₜ L.space)
    (hG : Continuous (fun z : I × L.space => G z.1 z.2))
    (hGi : Continuous (fun z : I × L.space => (G z.1).symm z.2))
    (hG0 : G 0 = Homeomorph.refl L.space)
    (track : ℝ × E → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ L.space))
    (hvalue : ∀ t : I, ∀ x : L.space, track ((t : ℝ), x) = (G t x : E)) :
    ∃ (H : I → K.space ≃ₜ K.space) (newTrack : ℝ × E → E),
      Continuous (fun z : I × K.space => H z.1 z.2) ∧
      Continuous (fun z : I × K.space => (H z.1).symm z.2) ∧
      H 0 = Homeomorph.refl K.space ∧
      FinitePiecewiseAffineOn newTrack (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
      (∀ t : I, ∀ x : K.space, newTrack ((t : ℝ), x) = (H t x : E)) ∧
      (∀ t : I, ∀ x : L.space, (H t ⟨x, hLK x.property⟩ : E) = G t x) ∧
      (∀ t : I, ∀ x : K.space, (x : E) ∉ L.space → H t x = x) := by
  classical
  let S : Set K.space := (Subtype.val : K.space → E) ⁻¹' L.space
  let B : L.space ≃ₜ S :=
    { toFun := fun x => ⟨⟨x, hLK x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let G' (t : I) : S ≃ₜ S := (B.symm.trans (G t)).trans B
  have hG' : Continuous (fun z : I × S => G' z.1 z.2) :=
    B.continuous.comp (hG.comp
      (continuous_fst.prodMk (B.symm.continuous.comp continuous_snd)))
  have hGi' : Continuous (fun z : I × S => (G' z.1).symm z.2) :=
    B.continuous.comp (hGi.comp
      (continuous_fst.prodMk (B.symm.continuous.comp continuous_snd)))
  have hG0' : G' 0 = Homeomorph.refl S := by
    apply Homeomorph.ext
    intro x
    change B (G 0 (B.symm x)) = x
    rw [hG0]
    exact B.apply_symm_apply x
  obtain ⟨H, hH, hHi, hH0, hHin, hHout⟩ :=
    UpperExtension.exists_clopen_motion_extension hclopen G' hG' hGi' 0 hG0'
  have hin (t : I) (x : L.space) :
      (H t ⟨x, hLK x.property⟩ : E) = G t x := by
    exact congrArg Subtype.val (hHin t (B x))
  let C : Set (ℝ × E) := Icc (0 : ℝ) 1 ×ˢ K.space
  let newTrack (z : ℝ × E) : E :=
    if hz : z ∈ C then H ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩ else 0
  have hnew (t : I) (x : K.space) : newTrack ((t : ℝ), x) = (H t x : E) := by
    simp only [newTrack, show ((t : ℝ), (x : E)) ∈ C from ⟨t.property, x.property⟩,
      dite_true]
  have hc : ContinuousOn newTrack C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hp : Continuous (fun z : C =>
        ((⟨z.val.1, z.property.1⟩ : I), (⟨z.val.2, z.property.2⟩ : K.space))) :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    apply (continuous_subtype_val.comp (hH.comp hp)).congr
    intro z
    exact (hnew ⟨z.val.1, z.property.1⟩ ⟨z.val.2, z.property.2⟩).symm
  have hnewPL : FinitePiecewiseAffineOn newTrack C := by
    apply CollarIsotopy.finitePiecewiseAffineOn_supported_track K hK
      (L.isCompact_space_of_finite hL).isClosed htrack hc
    · intro t ht x hx
      rw [hnew ⟨t, ht⟩ ⟨x, hx.1⟩, hvalue ⟨t, ht⟩ ⟨x, hx.2⟩]
      exact hin ⟨t, ht⟩ ⟨x, hx.2⟩
    · intro t ht x hx
      rw [hnew ⟨t, ht⟩ ⟨x, hx.1⟩]
      exact congrArg Subtype.val (hHout ⟨t, ht⟩ ⟨x, hx.1⟩ hx.2)
  exact ⟨H, newTrack, hH, hHi, hH0, hnewPL, hnew, hin, hHout⟩

end PoincareConjecture.M76
