import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PlanarDiskConvexContainment
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.AlexanderComplexityOrdinaryDiskBoundary

/-!
# Uniqueness of the actual planar disk with a prescribed rim

Two planar finite PL disks with the same complete boundary
are the same closed polygon inside. One affine retraction
returns this equality to the original height plane. See
Alexander 1924, pp. 6--8 and M76 derivation 248g.
-/

set_option autoImplicit false

open Set

namespace Set

/-- Actual finite PL disks in the real plane with the same
complete rim are equal. No common model chart or convexity
is assumed. See Alexander pp. 6--8 and derivation248g. -/
theorem IsFinitePLBallPair.eq_of_same_planar_rim {d e q : Set (ℝ × ℝ)}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (he : IsFinitePLBallPair (ℝ × ℝ) e q) :
    d = e := by
  obtain ⟨n, P, hPi, hPe, hPq⟩ := hd.exists_polygon_boundary
  have hdP : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) := by rwa [hPq]
  have heP : IsFinitePLBallPair (ℝ × ℝ) e (P.boundary ℝ) := by rwa [hPq]
  exact (hdP.eq_closure_polygon_inside P hPe hPi).trans
    (heP.eq_closure_polygon_inside P hPe hPi).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Two finite PL disks in the same nonconstant affine plane
of a three-dimensional space with the same complete rim are
equal as actual subsets. The coordinate retraction is shared
by both disks. See Alexander pp. 6--8 and derivation248g. -/
theorem IsFinitePLBallPair.eq_of_same_rim_in_affine_plane {d e q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (he : IsFinitePLBallPair (ℝ × ℝ) e q)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    {c : ℝ} (hdplane : d ⊆ {x | A x = c}) (heplane : e ⊆ {x | A x = c}) :
    d = e := by
  let B := A - AffineMap.const ℝ E c
  have hB : B.linear ≠ 0 := by simpa [B] using hA
  have hdB : d ⊆ {x | B x = 0} := by
    intro x hx
    change A x - c = 0
    exact sub_eq_zero.mpr (hdplane hx)
  have heB : e ⊆ {x | B x = 0} := by
    intro x hx
    change A x - c = 0
    exact sub_eq_zero.mpr (heplane hx)
  obtain ⟨a, r, _, hleft, _⟩ := B.exists_zeroLevel_coordinates hB
    (F := ℝ × ℝ) (by simp [hdim, Module.finrank_prod])
  have hrd := hd.affine_image r (hleft.injOn.mono hdB)
  have hre := he.affine_image r (hleft.injOn.mono heB)
  exact (hleft.injOn.image_eq_image_iff hdB heB).mp (hrd.eq_of_same_planar_rim hre)

end Set
