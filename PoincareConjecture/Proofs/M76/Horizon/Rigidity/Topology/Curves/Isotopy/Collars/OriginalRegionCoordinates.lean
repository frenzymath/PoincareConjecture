import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.FiniteDimensionalSelection
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts



set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

theorem exists_original_collar_extension_coordinates
    {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} {eps delta : ℝ} (heps : 0 < eps) (hed : eps ≤ delta)
    (c : E × ℝ → X)
    (hemb : IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) delta) => c z))
    (hmap : MapsTo c (K.space ×ˢ Icc (0 : ℝ) delta) R)
    (G : C(R, R))
    (m : (K.space ×ˢ Icc (0 : ℝ) eps) ≃ₜ (K.space ×ˢ Icc (0 : ℝ) eps))
    (hm : m.IsFinitePL)
    (hsmall : ∀ z : (K.space ×ˢ Icc (0 : ℝ) eps),
      (G ⟨c z, hmap ⟨z.property.1, z.property.2.1, z.property.2.2.trans hed⟩⟩ : X) = c (m z))
    (hout : ∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G x = x) :
    ∃ f : E × ℝ → E × ℝ,
      FinitePiecewiseAffineOn f (K.space ×ˢ Icc (0 : ℝ) delta) ∧
      MapsTo f (K.space ×ˢ Icc (0 : ℝ) delta) (K.space ×ˢ Icc (0 : ℝ) delta) ∧
      ∀ z : (K.space ×ˢ Icc (0 : ℝ) delta),
        c (f z) = (G ⟨c z, hmap z.property⟩ : X) := by
  classical
  let P := K.space ×ˢ Icc (0 : ℝ) eps
  let B := K.space ×ˢ Icc (0 : ℝ) delta
  have hPB : P ⊆ B := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hed⟩
  let f (z : E × ℝ) := if hz : z ∈ P then (m ⟨z, hz⟩ : E × ℝ) else z
  have hfP (z : P) : f z = (m z : E × ℝ) := by
    simp only [f, dif_pos z.property]
    rfl
  have hfout (z : E × ℝ) (hz : z ∉ P) : f z = z := by simp only [f, dif_neg hz]
  have hmaps : MapsTo f B B := by
    intro z hz
    by_cases hp : z ∈ P
    · rw [hfP ⟨z, hp⟩]
      exact hPB (m ⟨z, hp⟩).property
    · rw [hfout z hp]
      exact hz
  have hformula (z : B) : c (f z) = (G ⟨c z, hmap z.property⟩ : X) := by
    by_cases hp : (z : E × ℝ) ∈ P
    · rw [hfP ⟨z, hp⟩]
      exact (hsmall ⟨z, hp⟩).symm
    · have hn : c z ∉ c '' P := by
        rintro ⟨w, hw, heq⟩
        have he : (⟨w, hPB hw⟩ : B) = z := hemb.injective heq
        exact hp ((congrArg Subtype.val he) ▸ hw)
      rw [hfout z hp, hout _ hn]
  let fB : B → B := fun z => ⟨f z, hmaps z.property⟩
  have hfBc : Continuous fB := by
    apply hemb.continuous_iff.mpr
    have hcR : Continuous (fun z : B => (⟨c z, hmap z.property⟩ : R)) :=
      hemb.continuous.subtype_mk _
    exact ((continuous_subtype_val.comp G.continuous).comp hcR).congr
      (fun z => (hformula z).symm)
  have hfc : ContinuousOn f B := continuousOn_iff_continuous_domRestrict.mpr
    (continuous_subtype_val.comp hfBc)
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK (heps.trans_le hed)
  obtain ⟨fm, hfm, hfmv⟩ := hm
  have hid : FinitePiecewiseAffineOn (id : E × ℝ → E × ℝ) J.space :=
    (J.affineOnFaces_affine (ContinuousAffineMap.id ℝ (E × ℝ))).finitePiecewiseAffineOn hJ
  have hPclosed : IsClosed P := (K.isCompact_space_of_finite hK).isClosed.prod isClosed_Icc
  have hf : FinitePiecewiseAffineOn f J.space :=
    hid.closed_paste_on_carrier_finiteDimensional J hJ hPclosed hfm (hJs.symm ▸ hfc)
      (fun z hz => (hfP ⟨z, hz.2⟩).trans (hfmv ⟨z, hz.2⟩))
      (fun z hz => hfout z hz.2)
  exact ⟨f, hJs ▸ hf, hmaps, hformula⟩

end PoincareConjecture.M76.CollarIsotopy
