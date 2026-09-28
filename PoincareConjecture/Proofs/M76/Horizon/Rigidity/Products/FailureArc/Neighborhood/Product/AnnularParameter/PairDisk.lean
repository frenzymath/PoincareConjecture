import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.AnnularParameter

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem pairCoordinates_image_rim :
    pairCoordinates '' sphere (0 : V2) 1 = sphere (0 : P2) 1 := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (pairCoordinates_rim v).mp hv
  · intro hz
    obtain ⟨v, hv⟩ := pairCoordinates_rim_surjective ⟨z, hz⟩
    exact ⟨v, v.property, hv⟩

theorem pairCoordinates_image_disk :
    pairCoordinates '' closedBall (0 : V2) 1 = closedBall (0 : P2) 1 := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, pairCoordinates_norm] using hv
  · intro hz
    refine ⟨pairCoordinates.symm z, ?_, pairCoordinates.apply_symm_apply z⟩
    rw [mem_closedBall, dist_zero_right, ← pairCoordinates_norm,
      pairCoordinates.apply_symm_apply]
    simpa only [mem_closedBall, dist_zero_right] using hz

theorem pairDisk_isFinitePLBallPair :
    IsFinitePLBallPair P2 (closedBall (0 : P2) 1) (sphere (0 : P2) 1) := by
  have h := (isFinitePLBallPair_unit_cube (ι := Fin 2)).affine_image
    pairCoordinates.toContinuousAffineEquiv.toContinuousAffineMap
    pairCoordinates.injective.injOn
  change IsFinitePLBallPair V2 (pairCoordinates '' closedBall (0 : V2) 1)
    (pairCoordinates '' sphere (0 : V2) 1) at h
  rw [pairCoordinates_image_disk, pairCoordinates_image_rim] at h
  exact h.model_equiv pairCoordinates

theorem exists_pair_rim_triangulation :
    ∃ K : SimplicialComplex ℝ P2, K.faces.Finite ∧ K.space = sphere (0 : P2) 1 := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  let ha := K.affineOnFaces_affine pairCoordinates.toContinuousAffineEquiv.toContinuousAffineMap
  refine ⟨ha.embeddedImage pairCoordinates.injective.injOn,
    ha.embeddedImage_finite _ hK, ?_⟩
  exact (ha.embeddedImage_space _).trans (by
    change pairCoordinates '' K.space = _
    rw [hKs, pairCoordinates_image_rim])

end PoincareConjecture.M76.Dehn.Annuli.AnnularParameter
