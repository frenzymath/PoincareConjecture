import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLMinimum
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.SegmentStripProduct

/-!
# A finite PL square-shell sector with prescribed boundary values

The minimum of two positive-slope affine formulas maps the
unit interval times a radius interval onto the corresponding
trapezoidal square-shell sector. On each boundary radius the
map is the canonical affine parametrization of that square
edge, independent of the shell's other radius. See Hatcher
p. 7, Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace SquareShell

/-- The actual positive-slope longitudinal coordinate on a
square-shell sector. See M76 derivation 270. -/
noncomputable def coordinate (a b s r : ℝ) : ℝ :=
  min (2 * b * s - r) (2 * a * s + r - 2 * a)

/-- The rectangular source of the canonical shell-sector
chart. See M76 derivation 270. -/
def parameterRectangle (a b : ℝ) : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc a b

/-- The top sector of a closed square shell of positive
inner radius. See M76 derivation 270. -/
def sector (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc a b ∧ p.1 ∈ Icc (-p.2) p.2}

/-- The actual shell-sector coordinate map, retaining its
radius as the second coordinate. See M76 derivation 270. -/
noncomputable def sectorMap (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (coordinate a b p.1 p.2, p.2)

/-- Both affine slopes are positive, so the minimum is
strictly increasing in the longitudinal parameter everywhere.
See M76 derivation 270. -/
theorem strictMono_coordinate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
    StrictMono (fun s => coordinate a b s r) := by
  intro s t hst
  apply lt_min
  · exact lt_of_le_of_lt (min_le_left _ _) (by nlinarith)
  · exact lt_of_le_of_lt (min_le_right _ _) (by nlinarith)

/-- The two vertical sides map to the two radial corner
edges with the exact retained radius. See M76 derivation 270. -/
theorem coordinate_endpoints {a b r : ℝ} (hr : r ∈ Icc a b) :
    coordinate a b 0 r = -r ∧ coordinate a b 1 r = r := by
  constructor
  · unfold coordinate
    norm_num only [mul_zero, zero_sub, zero_add]
    exact min_eq_left (by linarith [hr.1])
  · unfold coordinate
    norm_num only [mul_one]
    have h : 2 * a + r - 2 * a = r := by ring
    rw [h]
    exact min_eq_right (by linarith [hr.2])

/-- Each complete interval fiber maps onto the whole square
edge at its prescribed radius. See M76 derivation 270. -/
theorem coordinate_image_Icc {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : r ∈ Icc a b) :
    (fun s => coordinate a b s r) '' Icc 0 1 = Icc (-r) r := by
  have hc : Continuous (fun s => coordinate a b s r) := by unfold coordinate; fun_prop
  rw [hc.continuousOn.image_Icc_of_monotoneOn zero_le_one
    ((strictMono_coordinate ha hb r).monotone.monotoneOn _),
    (coordinate_endpoints hr).1, (coordinate_endpoints hr).2]

/-- On the inner edge the exact formula is the canonical
affine parametrization of the radius-a square side. See
M76 derivation 270. -/
theorem coordinate_inner {a b s : ℝ} (hab : a ≤ b) (hs : s ∈ Icc 0 1) :
    coordinate a b s a = a * (2 * s - 1) := by
  unfold coordinate
  rw [min_eq_right (by nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs.1])]
  ring

/-- On the outer edge the exact formula is the canonical
affine parametrization of the radius-b square side. See
M76 derivation 270. -/
theorem coordinate_outer {a b s : ℝ} (hab : a ≤ b) (hs : s ∈ Icc 0 1) :
    coordinate a b s b = b * (2 * s - 1) := by
  have hnonneg : 0 ≤ (b - a) * (1 - s) :=
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hs.2)
  unfold coordinate
  rw [min_eq_left (by nlinarith)]
  ring

/-- The actual sector coordinate map is injective; its
second coordinate first determines the radius. See
M76 derivation 270. -/
theorem sectorMap_injective {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Function.Injective (sectorMap a b) := by
  intro p q he
  have hr := congrArg Prod.snd he
  have hs := congrArg Prod.fst he
  change p.2 = q.2 at hr
  change coordinate a b p.1 p.2 = coordinate a b q.1 q.2 at hs
  rw [← hr] at hs
  exact Prod.ext ((strictMono_coordinate ha hb p.2).injective hs) hr

/-- The exact image of the rectangular source is the full
closed trapezoidal sector. See M76 derivation 270. -/
theorem sectorMap_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sectorMap a b '' parameterRectangle a b = sector a b := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hq.2, ?_⟩
    change coordinate a b q.1 q.2 ∈ Icc (-q.2) q.2
    rw [← coordinate_image_Icc ha hb hq.2]
    exact mem_image_of_mem _ hq.1
  · rintro ⟨hr, hs⟩
    rw [← coordinate_image_Icc ha hb hr] at hs
    obtain ⟨s, hs, he⟩ := hs
    exact ⟨(s, p.2), ⟨hs, hr⟩, Prod.ext he rfl⟩

/-- The canonical sector map is finite PL on every actual
finite source complex, by its min-affine formula. See Hudson
pp. 15--19 and M76 derivation 270. -/
theorem finitePiecewiseAffineOn_sectorMap
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) (a b : ℝ) :
    FinitePiecewiseAffineOn (sectorMap a b) K.space := by
  let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let A := (2 * b) • x - y
  let B := (2 * a) • x + y - ContinuousAffineMap.const ℝ (ℝ × ℝ) (2 * a)
  have hA := (K.affineOnFaces_affine A).finitePiecewiseAffineOn hK
  have hB := (K.affineOnFaces_affine B).finitePiecewiseAffineOn hK
  have hy := (K.affineOnFaces_affine y).finitePiecewiseAffineOn hK
  exact (hA.min hB).prod_mk hy

/-- The min-affine formula constructs a finite PL chart of
the whole square-shell sector, with its actual values retained.
See Hatcher p. 7 and M76 derivation 270. -/
theorem exists_sector_homeomorph {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ e : parameterRectangle a b ≃ₜ sector a b, e.IsFinitePL ∧
      ∀ p, (e p : ℝ × ℝ) = sectorMap a b p := by
  have hex := PLStrip.exists_segmentProduct_homeomorph
    (show (0 : ℝ) ≠ 1 by norm_num) hab
  rw [segment_eq_Icc zero_le_one] at hex
  obtain ⟨D, hD, _⟩ := hex
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := hD.symm
  have hPL : FinitePiecewiseAffineOn (sectorMap a b) (parameterRectangle a b) := by
    change FinitePiecewiseAffineOn (sectorMap a b) (Icc 0 1 ×ˢ Icc a b)
    rw [← hKS]
    exact finitePiecewiseAffineOn_sectorMap K hK a b
  have he := hPL.exists_homeomorph_image (sectorMap_injective ha (ha.trans hab)).injOn
  rw [sectorMap_image ha (ha.trans hab)] at he
  exact he

end SquareShell
