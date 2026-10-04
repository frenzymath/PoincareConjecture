import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.TriangularRoof
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexSectionBallPair
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineLevelComplex

/-!
# Interval sections of a pointed triangular cap

The affine height with vertex values zero, one and two has
unique boundary extrema and a PL interval section at every
intermediate level. See Alexander 1924, p. 8, Hudson 1969,
pp. 12--19 and M76 derivation 167.
-/

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

/-- An affine cap height with a prescribed corner minimum and
three distinct vertex values. See M76 derivation 167. -/
def cornerHeight : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ + (2 : ℝ) • LinearMap.snd ℝ ℝ ℝ

/-- Coordinate formula for the pointed triangular height.
See M76 derivation 167. -/
theorem cornerHeight_apply (p : ℝ × ℝ) : cornerHeight p = p.1 + 2 * p.2 := rfl

/-- The entire triangular height lies between its two extremal
vertex values. See Alexander p. 8 and M76 derivation 167. -/
theorem cornerHeight_mem_Icc {p : ℝ × ℝ} (hp : p ∈ base) :
    cornerHeight p ∈ Icc 0 2 := by
  rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at hp
  rw [cornerHeight_apply]
  constructor <;> linarith [hp.1, hp.2.1, hp.2.2]

/-- The pointed corner is the unique zero of the height on the
triangle. See Alexander p. 8 and M76 derivation 167. -/
theorem cornerHeight_eq_zero_iff {p : ℝ × ℝ} (hp : p ∈ base) :
    cornerHeight p = 0 ↔ p = (0, 0) := by
  rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at hp
  constructor
  · intro h
    rw [cornerHeight_apply] at h
    apply Prod.ext <;> change _ = (0 : ℝ) <;> linarith [hp.1, hp.2.1]
  · rintro rfl
    norm_num [cornerHeight_apply]

/-- The other extreme corner is the unique maximum.
See Alexander p. 8 and M76 derivation 167. -/
theorem cornerHeight_eq_two_iff {p : ℝ × ℝ} (hp : p ∈ base) :
    cornerHeight p = 2 ↔ p = (0, 1) := by
  rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at hp
  constructor
  · intro h
    rw [cornerHeight_apply] at h
    apply Prod.ext
    · change p.1 = 0
      linarith [hp.1, hp.2.1, hp.2.2]
    · change p.2 = 1
      linarith [hp.1, hp.2.1, hp.2.2]
  · rintro rfl
    norm_num [cornerHeight_apply]

/-- Every strictly intermediate height line meets the actual
interior of the triangle, including the middle vertex height.
See Alexander p. 8 and M76 derivation 167. -/
theorem cornerHeight_interior_section_nonempty {t : ℝ} (ht : t ∈ Ioo 0 2) :
    (interior base ∩ {p | cornerHeight p = t}).Nonempty := by
  let x := t * (2 - t) / 4
  have hx : 0 < x := div_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) (by norm_num)
  have hxt : x < t := by dsimp [x]; nlinarith [ht.1, sq_nonneg t]
  have hx2 : x < 2 - t := by dsimp [x]; nlinarith [ht.2, sq_nonneg (2 - t)]
  refine ⟨(x, (t - x) / 2), ?_, ?_⟩
  · rw [interior_base]
    change 0 < min x (min ((t - x) / 2) (1 - x - (t - x) / 2))
    exact lt_min hx (lt_min (by linarith) (by linarith))
  · change x + 2 * ((t - x) / 2) = t
    ring

/-- Every intermediate height section is a finite PL interval
whose exact two-point boundary lies on the original triangle rim.
No regularity exclusion is made at the middle vertex height.
See Alexander p. 8 and M76 derivation 167. -/
theorem isFinitePLBallPair_cornerHeight_section {t : ℝ} (ht : t ∈ Ioo 0 2) :
    IsFinitePLBallPair ℝ (base ∩ {p | cornerHeight p = t})
      (frontier base ∩ {p | cornerHeight p = t}) := by
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := t⁻¹ • cornerHeight
  have hL (p : ℝ × ℝ) : L p = 1 ↔ cornerHeight p = t := by
    change t⁻¹ * cornerHeight p = 1 ↔ cornerHeight p = t
    rw [inv_mul_eq_iff_eq_mul₀ ht.1.ne', mul_one]
  let a : ℝ →ᴬ[ℝ] (ℝ × ℝ) := (ContinuousAffineMap.id ℝ ℝ).prod
    ((1 / 2 : ℝ) • (ContinuousAffineMap.const ℝ ℝ t - ContinuousAffineMap.id ℝ ℝ))
  let r : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  have ha (u : ℝ) : a u = (u, (t - u) / 2) := by
    apply Prod.ext
    · rfl
    · change (1 / 2 : ℝ) * (t - u) = (t - u) / 2
      ring
  have hleft : Function.LeftInverse r a := fun _ => rfl
  have hright : LeftInvOn a r {p | L p = 1} := by
    intro p hp
    have h := (hL p).mp hp
    rw [cornerHeight_apply] at h
    rw [ha]
    apply Prod.ext
    · rfl
    · change (t - p.1) / 2 = p.2
      linarith
  have hheight (u : ℝ) : L (a u) = 1 := by
    apply (hL _).mpr
    rw [ha, cornerHeight_apply]
    ring
  have hne : (interior base ∩ {p | L p = 1}).Nonempty := by
    obtain ⟨p, hp, hpt⟩ := cornerHeight_interior_section_nonempty ht
    exact ⟨p, hp, (hL p).mpr hpt⟩
  have hcopy := isFinitePLBallPair_base
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  obtain ⟨J, hJ, hJspace⟩ := K.exists_finite_affineLevel_complex hK L.toAffineMap 1
  rw [hspace] at hJspace
  have hcv : Convex ℝ base := by rw [base_eq_triangle]; exact convex_convexHull ℝ _
  have h := isCompact_base.isFinitePLBallPair_affine_section hcv L a r
    hleft hright hheight hne J hJ hJspace
  have hset : {p : ℝ × ℝ | L p = 1} = {p | cornerHeight p = t} := Set.ext hL
  rwa [hset] at h

end TriangularRoofModel
