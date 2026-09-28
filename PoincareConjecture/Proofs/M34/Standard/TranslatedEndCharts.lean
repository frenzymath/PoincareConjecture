import PoincareConjecture.Proofs.M34.Standard.EndExhaustion
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndTranslation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

def endReferenceRegion (e : StandardCylindricalEnd g) : Set StandardCapSpace :=
  e.coordinate '' (univ ×ˢ Ioo (3 : ℝ) 5)

def endReferenceSection (e : StandardCylindricalEnd g) : Set StandardCapSpace :=
  e.coordinate '' (univ ×ˢ ({4} : Set ℝ))

theorem endReferenceRegion_isOpen (e : StandardCylindricalEnd g) :
    IsOpen (endReferenceRegion e) :=
  end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioo)
    (fun _ hz => (by norm_num : (0 : ℝ) < 3).trans hz.2.1)

theorem endReferenceSection_isCompact (e : StandardCylindricalEnd g) :
    IsCompact (endReferenceSection e) := by
  apply (isCompact_univ.prod (isCompact_singleton (x := (4 : ℝ)))).image_of_continuousOn
  apply e.coordinate_smooth.continuousOn.mono
  intro z hz
  have hh : z.2 = 4 := hz.2
  refine ⟨mem_univ _, ?_⟩
  change -e.collar < z.2
  rw [hh]
  linarith [e.collar_pos]

theorem endReferenceSection_subset_region (e : StandardCylindricalEnd g) :
    endReferenceSection e ⊆ endReferenceRegion e := by
  apply image_mono
  rintro z ⟨_, hz⟩
  have hh : z.2 = 4 := hz
  exact ⟨mem_univ _, by rw [hh]; norm_num⟩

theorem endTranslation_contMDiffOn (e : StandardCylindricalEnd g)
    {s : ℝ} (hs : 3 ≤ s) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endAxialTranslation e (s - 4)) (endReferenceRegion e) := by
  rintro _ ⟨z, hz, rfl⟩
  have hheight : 3 < z.2 := hz.2.1
  have h := endAxialTranslation_contMDiffAt e (s - 4)
    (show 0 < z.2 by linarith) (show 0 < z.2 + (s - 4) by linarith)
  exact h.contMDiffWithinAt

theorem endTranslation_metric (e : StandardCylindricalEnd g) {s : ℝ} (hs : 3 ≤ s)
    {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e)
    (u v : TangentSpace (𝓡 3) x) :
    g.inner x u v = g.inner (endAxialTranslation e (s - 4) x)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (s - 4)) x u)
      (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (s - 4)) x v) := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hh : 3 < z.2 := hz.2.1
  exact endAxialTranslation_metric e (s - 4) (by linarith) (by linarith) u v

set_option backward.isDefEq.respectTransparency false in

theorem endTranslation_mfderiv_isInvertible (e : StandardCylindricalEnd g)
    {s : ℝ} (hs : 3 ≤ s) {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e) :
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (s - 4)) x).IsInvertible := by
  have hbij := g.mfderiv_bijective_of_pullback_eq g x
    (fun u v => (endTranslation_metric e hs hx u v).symm)
  let L : StandardCapSpace →L[ℝ] StandardCapSpace :=
    mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (s - 4)) x
  change L.IsInvertible
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2), rfl⟩

theorem endExhaustion_translation_eq (e : StandardCylindricalEnd g)
    {s : ℝ} (hs : 3 ≤ s) {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e) :
    endExhaustion e (endAxialTranslation e (s - 4) x) - (s - 4) = endExhaustion e x := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hh : 3 < z.2 := hz.2.1
  rw [endAxialTranslation_coordinate e (s - 4) (by linarith),
    endExhaustion_coordinate_of_two_le e (show 2 ≤ z.2 + (s - 4) by linarith),
    endExhaustion_coordinate_of_two_le e (by linarith)]
  dsimp only
  ring

theorem endTranslation_covers_tail (e : StandardCylindricalEnd g)
    (z : StandardCylinderSpace) :
    ∃ x ∈ endReferenceSection e,
      endAxialTranslation e (z.2 - 4) x = e.coordinate z := by
  refine ⟨e.coordinate (z.1, 4), ⟨(z.1, 4), ⟨mem_univ _, rfl⟩, rfl⟩, ?_⟩
  rw [endAxialTranslation_coordinate e (z.2 - 4) (by norm_num)]
  congr 1
  ext <;> simp

end PoincareConjecture.M34
