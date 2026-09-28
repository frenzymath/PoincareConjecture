import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndLocalDiffeomorph
import PoincareConjecture.Proofs.M34.Standard.CoordinateVolumeBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

noncomputable def endReferenceDiffeomorph (e : StandardCylindricalEnd g)
    {H : ℝ} (hH : 3 ≤ H) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := endAxialTranslation e (H - 4)
  invFun := endAxialTranslation e (-(H - 4))
  source := endReferenceRegion e
  target := e.coordinate '' (univ ×ˢ Ioo (H - 1) (H + 1))
  map_source' := by
    rintro _ ⟨z, hz, rfl⟩
    rw [endAxialTranslation_coordinate e (H - 4) (show 0 ≤ z.2 by linarith [hz.2.1])]
    exact ⟨(z.1, z.2 + (H - 4)), ⟨mem_univ _, by
      constructor <;> dsimp <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩
  map_target' := by
    rintro _ ⟨z, hz, rfl⟩
    rw [endAxialTranslation_coordinate e (-(H - 4)) (show 0 ≤ z.2 by linarith [hz.2.1])]
    exact ⟨(z.1, z.2 + -(H - 4)), ⟨mem_univ _, by
      constructor <;> dsimp <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩
  left_inv' := by
    rintro _ ⟨z, hz, rfl⟩
    rw [endAxialTranslation_coordinate e (H - 4) (show 0 ≤ z.2 by linarith [hz.2.1]),
      endAxialTranslation_coordinate e (-(H - 4))
        (show 0 ≤ z.2 + (H - 4) by linarith [hz.2.1])]
    congr 1
    apply Prod.ext
    · rfl
    · dsimp
      ring
  right_inv' := by
    rintro _ ⟨z, hz, rfl⟩
    rw [endAxialTranslation_coordinate e (-(H - 4))
        (show 0 ≤ z.2 by linarith [hz.2.1]),
      endAxialTranslation_coordinate e (H - 4)
        (show 0 ≤ z.2 + -(H - 4) by linarith [hz.2.1])]
    congr 1
    apply Prod.ext
    · rfl
    · dsimp
      ring
  open_source := endReferenceRegion_isOpen e
  open_target := end_isOpen_coordinate_image e (isOpen_univ.prod isOpen_Ioo)
    (fun z hz => by linarith [hz.2.1])
  contMDiffOn_toFun := endTranslation_contMDiffOn e hH
  contMDiffOn_invFun := by
    rintro _ ⟨z, hz, rfl⟩
    exact (endAxialTranslation_contMDiffAt e (-(H - 4))
      (by linarith [hz.2.1]) (by linarith [hz.2.1])).contMDiffWithinAt

theorem endReferenceDiffeomorph_pullback (e : StandardCylindricalEnd g)
    {H : ℝ} (hH : 3 ≤ H) {x : StandardCapSpace} (hx : x ∈ endReferenceRegion e) :
    M10.pullbackMetricForm g (endReferenceDiffeomorph e hH) x =
      M10.pullbackMetricForm g id x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change g.inner (endAxialTranslation e (H - 4) x)
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (H - 4)) x v)
    (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e (H - 4)) x w) =
      g.inner x (mfderiv (𝓡 3) (𝓡 3) id x v) (mfderiv (𝓡 3) (𝓡 3) id x w)
  rw [mfderiv_id]
  exact (endTranslation_metric e hH hx v w).symm

end PoincareConjecture.M34
