import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndTranslationCalculus
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EnergyCutoffs

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

def endClosedSlab (a b : ℝ) : Set StandardCapSpace :=
  e.coordinate '' (univ ×ˢ Icc a b)

theorem endClosedSlab_isCompact {a b : ℝ} (ha : 0 ≤ a) :
    IsCompact (endClosedSlab e a b) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply e.coordinate_smooth.continuousOn.mono
  intro z hz
  refine ⟨mem_univ _, ?_⟩
  change -e.collar < z.2
  have hh : a ≤ z.2 := hz.2.1
  linarith [e.collar_pos]

theorem endClosedSlab_subset_reference {a b : ℝ} (ha : 3 < a) (hb : b < 5) :
    endClosedSlab e a b ⊆ endReferenceRegion e := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩, rfl⟩

theorem endClosedSlab_translation {a b : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    endAxialTranslation e r '' endClosedSlab e a b = endClosedSlab e (a + r) (b + r) := by
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [endAxialTranslation_coordinate e r (ha.trans hz.2.1)]
    refine ⟨(z.1, z.2 + r), ⟨mem_univ _, ?_⟩, rfl⟩
    constructor <;> dsimp <;> linarith [hz.2.1, hz.2.2]
  · rintro _ ⟨z, hz, rfl⟩
    let w : StandardCylinderSpace := (z.1, z.2 - r)
    have hw : w ∈ univ ×ˢ Icc a b := by
      have hl : a + r ≤ z.2 := hz.2.1
      have hu : z.2 ≤ b + r := hz.2.2
      exact ⟨mem_univ _, by dsimp [w]; constructor <;> linarith⟩
    refine ⟨e.coordinate w, ⟨w, hw, rfl⟩, ?_⟩
    rw [endAxialTranslation_coordinate e r (ha.trans hw.2.1)]
    congr 1
    ext <;> simp [w]

theorem endAxialTranslation_injOn_reference (r : ℝ) (hr : -3 < r) :
    InjOn (endAxialTranslation e r) (endReferenceRegion e) := by
  intro x hx y hy hxy
  have hinv (z : StandardCapSpace) (hz : z ∈ endReferenceRegion e) :
      endAxialTranslation e (-r) (endAxialTranslation e r z) = z := by
    rw [endAxialTranslation_comp_reference e r hr (-r) hz, add_neg_cancel,
      endAxialTranslation_zero_reference e hz]
  have hh := congrArg (endAxialTranslation e (-r)) hxy
  rwa [hinv x hx, hinv y hy] at hh

theorem endEnergyCutoff_tsupport_subset_slab :
    tsupport (endEnergyCutoff e) ⊆ endClosedSlab e (31 / 10) (49 / 10) := by
  intro x hx
  have hheight : endExhaustion e x ∈ Icc (41 / 10 : ℝ) (59 / 10) :=
    endEnergyCutoff_tsupport e hx
  obtain ⟨z, hz, hzx, hvalue⟩ := endExhaustion_large_coordinate e
    (show 3 < endExhaustion e x by have hh := hheight.1; linarith)
  refine ⟨z, ⟨mem_univ _, ?_⟩, hzx⟩
  rw [hvalue] at hheight
  constructor <;> linarith [hheight.1, hheight.2]

end PoincareConjecture.M34
