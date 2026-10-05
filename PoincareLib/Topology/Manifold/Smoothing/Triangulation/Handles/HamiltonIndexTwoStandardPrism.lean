import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.PLBallBoundaryDiskComplement
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateHalfBoxes
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionBallInterior

/-!
# The literal square prisms in the index-two placement

Interval products and the checked complementary-boundary-disk theorem
give the whole standard middle ball and both complete outer cap disks.
See Hamilton 1976, pp.67--68 and M76 derivation338.
-/

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace PoincareMT.M76.HamiltonIndexTwoStandard

local notation "P" => ((ℝ × ℝ) × ℝ)

/-- The actual square prism. See Hamilton pp.67--68 and derivation338. -/
def prism (a b : ℝ) : Set P := base 1 ×ˢ Icc a b

/-- The full lateral patch of the prism. See derivation338. -/
def band (a b : ℝ) : Set P := baseBoundary 1 ×ˢ Icc a b

/-- A complete marked end disk. See derivation338. -/
def endDisk (a : ℝ) : Set P := base 1 ×ˢ {a}

/-- The complete square rim of an end disk. See derivation338. -/
def endRim (a : ℝ) : Set P := baseBoundary 1 ×ˢ {a}

/-- The lower outer disk, including all lateral faces. See derivation338. -/
def lowerOuter (a b : ℝ) : Set P := band a b ∪ endDisk a

/-- The upper outer disk, including all lateral faces. See derivation338. -/
def upperOuter (a b : ℝ) : Set P := band a b ∪ endDisk b

private theorem base_boundary_subset : baseBoundary 1 ⊆ base 1 :=
  (base_ballPair (by norm_num : (0 : ℝ) < 1)).1

/-- The whole prism has its full side and both marked end disks as
boundary. See Hudson pp.15--19 and derivation338. -/
theorem prism_ballPair {a b : ℝ} (hab : a < b) :
    IsFinitePLBallPair P (prism a b) ((band a b ∪ endDisk a) ∪ endDisk b) := by
  have h := (base_ballPair (by norm_num : (0 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc hab)
  have heq : (baseBoundary 1 ×ˢ Icc a b) ∪ (base 1 ×ˢ {a, b}) =
      (band a b ∪ endDisk a) ∪ endDisk b := by
    ext x
    simp only [band, endDisk, mem_prod, mem_union, mem_insert_iff, mem_singleton_iff]
    tauto
  rwa [heq] at h

/-- The complete planar end disk is a finite PL disk with its exact
square rim. See Hudson pp.15--19 and derivation338. -/
theorem endDisk_ballPair (a : ℝ) :
    IsFinitePLBallPair (ℝ × ℝ) (endDisk a) (endRim a) :=
  (base_ballPair (by norm_num : (0 : ℝ) < 1)).prod_singleton a

/-- Removing the upper end's relative interior leaves precisely the
whole lower outer disk. See Alexander pp.6--8 and derivation338. -/
theorem lowerOuter_ballPair {a b : ℝ} (hab : a < b) :
    IsFinitePLBallPair (ℝ × ℝ) (lowerOuter a b) (endRim b) := by
  have hdS : endDisk b ⊆ (band a b ∪ endDisk a) ∪ endDisk b :=
    subset_union_right
  have hout : (((band a b ∪ endDisk a) ∪ endDisk b) \ endDisk b).Nonempty := by
    refine ⟨((0, 0), a), Or.inl (Or.inr ?_), ?_⟩
    · norm_num [endDisk, base]
    · intro hx
      have hx' : a = b := hx.2
      exact hab.ne hx'
  have h := (prism_ballPair hab).boundary_disk_complement
    (by simp [Module.finrank_prod]) (endDisk_ballPair b) hdS hout
  have heq : ((band a b ∪ endDisk a) ∪ endDisk b) \ (endDisk b \ endRim b) =
      lowerOuter a b := by
    ext x
    change ((((x.1 ∈ baseBoundary 1 ∧ x.2 ∈ Icc a b) ∨
      (x.1 ∈ base 1 ∧ x.2 = a)) ∨ (x.1 ∈ base 1 ∧ x.2 = b)) ∧
      ¬ ((x.1 ∈ base 1 ∧ x.2 = b) ∧ ¬ (x.1 ∈ baseBoundary 1 ∧ x.2 = b))) ↔
      (x.1 ∈ baseBoundary 1 ∧ x.2 ∈ Icc a b) ∨ (x.1 ∈ base 1 ∧ x.2 = a)
    constructor
    · rintro ⟨(hx | hx) | hx, hnot⟩
      · exact Or.inl hx
      · exact Or.inr hx
      · have hq : x.1 ∈ baseBoundary 1 := by
          by_contra hn
          exact hnot ⟨hx, fun h => hn h.1⟩
        refine Or.inl ⟨hq, ?_⟩
        rw [hx.2]
        exact ⟨hab.le, le_rfl⟩
    · rintro (hx | hx)
      · exact ⟨Or.inl (Or.inl hx), fun h => h.2 ⟨hx.1, h.1.2⟩⟩
      · refine ⟨Or.inl (Or.inr hx), ?_⟩
        intro h
        exact hab.ne (hx.2.symm.trans h.1.2)
  rwa [heq] at h

/-- Removing the lower end's relative interior leaves precisely the
whole upper outer disk. See Alexander pp.6--8 and derivation338. -/
theorem upperOuter_ballPair {a b : ℝ} (hab : a < b) :
    IsFinitePLBallPair (ℝ × ℝ) (upperOuter a b) (endRim a) := by
  have hdS : endDisk a ⊆ (band a b ∪ endDisk a) ∪ endDisk b :=
    (subset_union_right : endDisk a ⊆ band a b ∪ endDisk a).trans subset_union_left
  have hout : (((band a b ∪ endDisk a) ∪ endDisk b) \ endDisk a).Nonempty := by
    refine ⟨((0, 0), b), Or.inr ?_, ?_⟩
    · norm_num [endDisk, base]
    · intro hx
      have hx' : b = a := hx.2
      exact hab.ne hx'.symm
  have h := (prism_ballPair hab).boundary_disk_complement
    (by simp [Module.finrank_prod]) (endDisk_ballPair a) hdS hout
  have heq : ((band a b ∪ endDisk a) ∪ endDisk b) \ (endDisk a \ endRim a) =
      upperOuter a b := by
    ext x
    change ((((x.1 ∈ baseBoundary 1 ∧ x.2 ∈ Icc a b) ∨
      (x.1 ∈ base 1 ∧ x.2 = a)) ∨ (x.1 ∈ base 1 ∧ x.2 = b)) ∧
      ¬ ((x.1 ∈ base 1 ∧ x.2 = a) ∧ ¬ (x.1 ∈ baseBoundary 1 ∧ x.2 = a))) ↔
      (x.1 ∈ baseBoundary 1 ∧ x.2 ∈ Icc a b) ∨ (x.1 ∈ base 1 ∧ x.2 = b)
    constructor
    · rintro ⟨(hx | hx) | hx, hnot⟩
      · exact Or.inl hx
      · have hq : x.1 ∈ baseBoundary 1 := by
          by_contra hn
          exact hnot ⟨hx, fun h => hn h.1⟩
        refine Or.inl ⟨hq, ?_⟩
        rw [hx.2]
        exact ⟨le_rfl, hab.le⟩
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨Or.inl (Or.inl hx), fun h => h.2 ⟨hx.1, h.1.2⟩⟩
      · refine ⟨Or.inr hx, ?_⟩
        intro h
        exact hab.ne (h.1.2.symm.trans hx.2)
  rwa [heq] at h

private theorem finitePL_identity_of_ball {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s b : Set E} (h : IsFinitePLBallPair V s b) :
    FinitePiecewiseAffineOn (id : E → E) s := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := h
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩

/-- The whole side annulus has a finite triangulation obtained from
the exact square frontier and the interval. See derivation338. -/
theorem band_identity_finitePL {a b : ℝ} (hab : a < b) :
    FinitePiecewiseAffineOn (id : P → P) (band a b) := by
  have hbase := base_ballPair (by norm_num : (0 : ℝ) < 1)
  obtain ⟨K, hK, hspace, _⟩ := finitePL_identity_of_ball hbase
  let J := K.frontierSubcomplex (base 1)
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite (base 1) hK
  have hJspace : J.space = baseBoundary 1 :=
    (K.frontierSubcomplex_space hbase.isCompact.isClosed
      ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1))
      (hbase.isConnected_interior_of_finrank_eq rfl).nonempty hspace).trans
      (hbase.frontier_eq_of_finrank_eq rfl)
  have hq : FinitePiecewiseAffineOn (id : (ℝ × ℝ) → (ℝ × ℝ)) (baseBoundary 1) :=
    ⟨J, hJ, hJspace, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ (ℝ × ℝ))⟩
  exact (hq.prodMap (finitePL_identity_of_ball (isFinitePLBallPair_Icc hab))).congr
    (fun _ _ => rfl)

end PoincareMT.M76.HamiltonIndexTwoStandard
