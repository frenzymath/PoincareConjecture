import PoincareConjecture.Proofs.M34.Standard.TranslatedEndCharts
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

theorem endAxialTranslation_isLocalDiffeomorphAt (e : StandardCylindricalEnd g)
    (s : ℝ) {z : StandardCylinderSpace} (hz : 0 < z.2) (hsz : 0 < z.2 + s) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (endAxialTranslation e s)
      (e.coordinate z) := by
  let V : ℝ → Set StandardCylinderSpace := fun r => univ ×ˢ Ioi (max 0 r)
  have hpos : ∀ r, ∀ w ∈ V r, 0 < w.2 :=
    fun _ _ hw => (le_max_left _ _).trans_lt hw.2
  have hshift : ∀ r, ∀ w ∈ V (-r), 0 < w.2 + r := by
    intro r w hw
    have hh := (le_max_right 0 (-r)).trans_lt hw.2
    linarith
  let D : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
    { toFun := endAxialTranslation e s
      invFun := endAxialTranslation e (-s)
      source := e.coordinate '' V (-s)
      target := e.coordinate '' V s
      map_source' := by
        rintro _ ⟨w, hw, rfl⟩
        rw [endAxialTranslation_coordinate e s (hpos _ _ hw).le]
        refine ⟨(w.1, w.2 + s), ⟨mem_univ _, ?_⟩, rfl⟩
        change max 0 s < w.2 + s
        exact max_lt_iff.mpr ⟨hshift s w hw, by have hh := hpos _ _ hw; linarith⟩
      map_target' := by
        rintro _ ⟨w, hw, rfl⟩
        rw [endAxialTranslation_coordinate e (-s) (hpos _ _ hw).le]
        refine ⟨(w.1, w.2 + -s), ⟨mem_univ _, ?_⟩, rfl⟩
        change max 0 (-s) < w.2 + -s
        have hh := (le_max_right 0 s).trans_lt hw.2
        exact max_lt_iff.mpr ⟨by linarith, by have hp := hpos _ _ hw; linarith⟩
      left_inv' := by
        rintro _ ⟨w, hw, rfl⟩
        rw [endAxialTranslation_coordinate e s (hpos _ _ hw).le,
          endAxialTranslation_coordinate e (-s) (hshift s w hw).le]
        simp
      right_inv' := by
        rintro _ ⟨w, hw, rfl⟩
        have hh := (le_max_right 0 s).trans_lt hw.2
        rw [endAxialTranslation_coordinate e (-s) (hpos _ _ hw).le,
          endAxialTranslation_coordinate e s (show 0 ≤ w.2 + -s by linarith)]
        simp
      open_source := end_isOpen_coordinate_image e
        (isOpen_univ.prod isOpen_Ioi) (hpos (-s))
      open_target := end_isOpen_coordinate_image e
        (isOpen_univ.prod isOpen_Ioi) (hpos s)
      contMDiffOn_toFun := by
        rintro _ ⟨w, hw, rfl⟩
        exact (endAxialTranslation_contMDiffAt e s
          (hpos _ _ hw) (hshift s w hw)).contMDiffWithinAt
      contMDiffOn_invFun := by
        rintro _ ⟨w, hw, rfl⟩
        have hh := (le_max_right 0 s).trans_lt hw.2
        exact (endAxialTranslation_contMDiffAt e (-s)
          (hpos _ _ hw) (by linarith)).contMDiffWithinAt }
  refine ⟨D, ⟨z, ⟨mem_univ _, max_lt_iff.mpr ⟨hz, by linarith⟩⟩, rfl⟩, ?_⟩
  exact fun _ _ => rfl

instance endReferenceRegion_nonempty (e : StandardCylindricalEnd g) :
    Nonempty (endReferenceRegion e) := by
  let u : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact ⟨⟨e.coordinate (u, 4), ⟨(u, 4), ⟨mem_univ _, by norm_num⟩, rfl⟩⟩⟩

theorem endReferenceTranslation_isLocalDiffeomorph (e : StandardCylindricalEnd g)
    {s : ℝ} (hs : -3 < s) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : endReferenceRegion e => endAxialTranslation e s x) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  have hi := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3)
    (endReferenceRegion e) (endReferenceRegion_isOpen e) ∞ x
  have ht : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (endAxialTranslation e s)
      (x : StandardCapSpace) := by
    obtain ⟨z, hz, hx⟩ := x.property
    rw [← hx]
    have hh : 3 < z.2 := hz.2.1
    exact endAxialTranslation_isLocalDiffeomorphAt e s (by linarith) (by linarith)
  exact hi.comp (𝓡 3) StandardCapSpace ht

end PoincareConjecture.M34
