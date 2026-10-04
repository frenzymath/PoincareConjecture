import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.TriangularPointedHeight
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Affine.AffineConvexSphereCapDisks

/-!
# Sublevel arcs of the pointed triangle's rim

The convex-frontier cap theorem in ambient dimension two gives
an exact finite PL interval with the height section as its two
endpoints. See Alexander 1924, p. 8, Hudson 1969, pp. 15--19
and M76 derivation 172.
-/

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

/-- The pointed height's rim sublevel at every intermediate
height is a finite PL interval with its exact level endpoints.
The middle vertex height is included. See Alexander p. 8 and
M76 derivation 172. -/
theorem isFinitePLBallPair_cornerHeight_rim_sublevel {t : ℝ} (ht : t ∈ Ioo 0 2) :
    IsFinitePLBallPair ℝ (frontier base ∩ {p | cornerHeight p ≤ t})
      (frontier base ∩ {p | cornerHeight p = t}) := by
  have hmid : (t + 2) / 2 ∈ Ioo (0 : ℝ) 2 := by
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨p, hp, hpt⟩ := cornerHeight_interior_section_nonempty hmid
  obtain ⟨q, hq, hqt⟩ := cornerHeight_interior_section_nonempty ht
  let A := AffineMap.const ℝ (ℝ × ℝ) t - cornerHeight.toAffineMap
  have hneg : ∃ p ∈ interior base, A p < 0 := by
    refine ⟨p, hp, ?_⟩
    change t - cornerHeight p < 0
    change cornerHeight p = (t + 2) / 2 at hpt
    linarith [ht.2]
  have hplane : ∃ q ∈ interior base, A q = 0 := by
    exact ⟨q, hq, sub_eq_zero.mpr hqt.symm⟩
  have hcopy := isFinitePLBallPair_base
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  have hcv : Convex ℝ base := by rw [base_eq_triangle]; exact convex_convexHull ℝ _
  have h := K.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ) hK isCompact_base
    hcv hspace A hneg hplane (by simp)
  have hcap : {p : ℝ × ℝ | 0 ≤ A p} = {p | cornerHeight p ≤ t} := by
    ext p
    change 0 ≤ t - cornerHeight p ↔ cornerHeight p ≤ t
    exact sub_nonneg
  have hrim : {p : ℝ × ℝ | A p = 0} = {p | cornerHeight p = t} := by
    ext p
    exact sub_eq_zero.trans eq_comm
  rwa [hcap, hrim] at h

/-- The complementary pointed rim superlevel is a finite PL
interval with the same exact level endpoints, including the
middle vertex height. See Alexander p. 8 and derivation 226. -/
theorem isFinitePLBallPair_cornerHeight_rim_superlevel {t : ℝ} (ht : t ∈ Ioo 0 2) :
    IsFinitePLBallPair ℝ (frontier base ∩ {p | t ≤ cornerHeight p})
      (frontier base ∩ {p | cornerHeight p = t}) := by
  have hmid : t / 2 ∈ Ioo (0 : ℝ) 2 := by
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨p, hp, hpt⟩ := cornerHeight_interior_section_nonempty hmid
  obtain ⟨q, hq, hqt⟩ := cornerHeight_interior_section_nonempty ht
  let A := cornerHeight.toAffineMap - AffineMap.const ℝ (ℝ × ℝ) t
  have hneg : ∃ p ∈ interior base, A p < 0 := by
    refine ⟨p, hp, ?_⟩
    change cornerHeight p - t < 0
    change cornerHeight p = t / 2 at hpt
    linarith [ht.1]
  have hplane : ∃ q ∈ interior base, A q = 0 :=
    ⟨q, hq, sub_eq_zero.mpr hqt⟩
  have hcopy := isFinitePLBallPair_base
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  have hcv : Convex ℝ base := by rw [base_eq_triangle]; exact convex_convexHull ℝ _
  have h := K.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ) hK isCompact_base
    hcv hspace A hneg hplane (by simp)
  have hcap : {p : ℝ × ℝ | 0 ≤ A p} = {p | t ≤ cornerHeight p} := by
    ext p
    change 0 ≤ cornerHeight p - t ↔ t ≤ cornerHeight p
    exact sub_nonneg
  have hrim : {p : ℝ × ℝ | A p = 0} = {p | cornerHeight p = t} := by
    ext p
    exact sub_eq_zero
  rwa [hcap, hrim] at h

end TriangularRoofModel
