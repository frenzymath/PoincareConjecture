import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Original.AnnularExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.Tracks



set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "Ann" => squareAnnulus 8 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isFinitePL_originalAnnularExtension
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (A : Ann ≃ₜ C) (hA : A.IsFinitePL)
    (hCK : C ⊆ K.space) (hC : IsClosed C)
    (hmark : IsOpen ((Subtype.val : K.space → E) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x) :
    (originalAnnularExtension A hCK hC hmark G hfix).IsFinitePL := by
  classical
  have hconj : (A.symm.trans (G.trans A)).IsFinitePL := hA.symm.trans (hG.trans hA)
  obtain ⟨f, hf, hfv⟩ := hconj
  let H := originalAnnularExtension A hCK hC hmark G hfix
  let g (x : E) : E := if hx : x ∈ K.space then (H ⟨x, hx⟩ : E) else 0
  have hgv (x : K.space) : g x = (H x : E) := by simp only [g, dif_pos x.property]
  have hgc : ContinuousOn g K.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp H.continuous).congr (fun x => (hgv x).symm)
  have hid : FinitePiecewiseAffineOn (id : E → E) K.space :=
    (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hK
  refine ⟨g, hid.closed_paste_on_carrier_finiteDimensional K hK hC hf hgc ?_ ?_,
    fun x => (hgv x).symm⟩
  · intro x hx
    rw [hgv ⟨x, hx.1⟩, ← hfv ⟨x, hx.2⟩]
    have hval : (⟨A (A.symm ⟨x, hx.2⟩), hCK (A (A.symm ⟨x, hx.2⟩)).property⟩ :
        K.space) = ⟨x, hx.1⟩ := by
      apply Subtype.ext
      exact congrArg (fun y : C => (y : E)) (A.apply_symm_apply ⟨x, hx.2⟩)
    exact congrArg Subtype.val (by
      simpa only [hval] using
        originalAnnularExtension_apply A hCK hC hmark G hfix (A.symm ⟨x, hx.2⟩))
  · intro x hx
    rw [hgv ⟨x, hx.1⟩]
    exact congrArg Subtype.val
      (originalAnnularExtension_fixed_off_mark A hCK hC hmark G hfix ⟨x, hx.1⟩
        (fun hm => hx.2 (originalAnnulusOpenMark_subset A hm)))

theorem exists_originalAnnularExtension_joint_finitePL
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (A : Ann ≃ₜ C) (hA : A.IsFinitePL)
    (hCK : C ⊆ K.space) (hC : IsClosed C)
    (hmark : IsOpen ((Subtype.val : K.space → E) ⁻¹' originalAnnulusOpenMark A))
    (G : I → Ann ≃ₜ Ann) (hc : Continuous (fun z : I × Ann => G z.1 z.2))
    (hfix : ∀ t (x : Ann), depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G t x = x)
    (track : (ℝ × (ℝ × ℝ)) → (ℝ × ℝ))
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ Ann))
    (hvalue : ∀ t : I, ∀ x : Ann, track ((t : ℝ), x) = (G t x : ℝ × ℝ)) :
    ∃ g : (ℝ × E) → E,
      FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
      ∀ t : I, ∀ x : K.space, g ((t : ℝ), x) =
        (originalAnnularExtension A hCK hC hmark (G t) (hfix t) x : E) := by
  classical
  obtain ⟨f, hf, hfv⟩ := CollarIsotopy.exists_conjugate_joint_finitePL
    A hA G track htrack hvalue
  let H (t : I) := originalAnnularExtension A hCK hC hmark (G t) (hfix t)
  let g (z : ℝ × E) : E := if hz : z ∈ Icc (0 : ℝ) 1 ×ˢ K.space then
    (H ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩ : E) else 0
  have hgv (t : I) (x : K.space) : g ((t : ℝ), x) = (H t x : E) := by
    simp only [g, dif_pos (show ((t : ℝ), (x : E)) ∈
      Icc (0 : ℝ) 1 ×ˢ K.space from ⟨t.property, x.property⟩)]
  have hg : ContinuousOn g (Icc (0 : ℝ) 1 ×ˢ K.space) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let P := Homeomorph.Set.prod (Icc (0 : ℝ) 1) K.space
    have h := continuous_subtype_val.comp
      ((continuous_originalAnnularExtension A hCK hC hmark G hc hfix).comp P.continuous)
    exact h.congr (fun z => (hgv ⟨z.1.1, z.2.1⟩ ⟨z.1.2, z.2.2⟩).symm)
  refine ⟨g, CollarIsotopy.finitePiecewiseAffineOn_supported_track K hK hC hf hg ?_ ?_, hgv⟩
  · intro t ht x hx
    rw [hgv ⟨t, ht⟩ ⟨x, hx.1⟩, hfv ⟨t, ht⟩ ⟨x, hx.2⟩]
    have hval : (⟨A (A.symm ⟨x, hx.2⟩), hCK (A (A.symm ⟨x, hx.2⟩)).property⟩ :
        K.space) = ⟨x, hx.1⟩ := by
      apply Subtype.ext
      exact congrArg (fun y : C => (y : E)) (A.apply_symm_apply ⟨x, hx.2⟩)
    exact congrArg Subtype.val (by
      simpa only [hval] using
        originalAnnularExtension_apply A hCK hC hmark (G ⟨t, ht⟩)
          (hfix ⟨t, ht⟩) (A.symm ⟨x, hx.2⟩))
  · intro t ht x hx
    rw [hgv ⟨t, ht⟩ ⟨x, hx.1⟩]
    exact congrArg Subtype.val
      (originalAnnularExtension_fixed_off_mark A hCK hC hmark (G ⟨t, ht⟩)
        (hfix ⟨t, ht⟩) ⟨x, hx.1⟩
        (fun hm => hx.2 (originalAnnulusOpenMark_subset A hm)))

end PoincareConjecture.M76.Dehn
