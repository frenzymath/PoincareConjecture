


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.VertexPatches








set_option autoImplicit false
open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch

def sectorInterval (c w : ℝ) (i : Bool) : Set ℝ :=
  if i then Ioo c (c + w) else Ioo (c - w) c

def closedSectorInterval (c w : ℝ) (i : Bool) : Set ℝ :=
  if i then Icc c (c + w) else Icc (c - w) c

theorem sectorInterval_subset_closed (c w : ℝ) (i : Bool) :
    sectorInterval c w i ⊆ closedSectorInterval c w i := by
  cases i <;> exact Ioo_subset_Icc_self

theorem closedSectorInterval_subset (c w : ℝ) (i : Bool) (hw : 0 ≤ w) :
    closedSectorInterval c w i ⊆ Icc (c - w) (c + w) := by
  cases i <;> intro x hx <;> change _ ≤ x ∧ x ≤ _ at hx ⊢ <;>
    constructor <;> linarith [hx.1, hx.2]

theorem closure_sectorInterval (c : ℝ) {w : ℝ} (hw : 0 < w) (i : Bool) :
    closure (sectorInterval c w i) = closedSectorInterval c w i := by
  cases i <;> exact closure_Ioo (by linarith)

theorem sectorInterval_connected (c : ℝ) {w : ℝ} (hw : 0 < w) (i : Bool) :
    IsPathConnected (sectorInterval c w i) := by
  cases i <;> exact (convex_Ioo _ _).isPathConnected (nonempty_Ioo.mpr (by linarith))

theorem center_mem_closedSectorInterval (c : ℝ) {w : ℝ} (hw : 0 ≤ w) (i : Bool) :
    c ∈ closedSectorInterval c w i := by
  cases i <;> constructor <;> linarith

theorem ne_center_of_mem_sectorInterval {c w x : ℝ} {i : Bool}
    (hx : x ∈ sectorInterval c w i) : x ≠ c := by
  cases i
  · exact ne_of_lt hx.2
  · exact ne_of_gt hx.1

theorem exists_mem_closedSectorInterval {c w x : ℝ}
    (hx : x ∈ Icc (c - w) (c + w)) : ∃ i, x ∈ closedSectorInterval c w i := by
  by_cases hcx : c ≤ x
  · exact ⟨true, hcx, hx.2⟩
  · exact ⟨false, hx.1, (lt_of_not_ge hcx).le⟩

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  {r : M → ℝ} {p : M}

variable (P : ChartCircleArrangementVertexPatch r p)


noncomputable def productCoordinates : OpenPartialHomeomorph (ℝ × ℝ) M :=
  collarParameterEquiv.symm.toHomeomorph.toOpenPartialHomeomorph.trans P.coordinates

def sectorBox (i : Bool × Bool) : Set (ℝ × ℝ) :=
  sectorInterval P.center.1 P.width i.1 ×ˢ sectorInterval P.center.2 P.width i.2

def closedSectorBox (i : Bool × Bool) : Set (ℝ × ℝ) :=
  closedSectorInterval P.center.1 P.width i.1 ×ˢ
    closedSectorInterval P.center.2 P.width i.2


def sector (i : Bool × Bool) : Set M := P.productCoordinates '' P.sectorBox i


def closedSector (i : Bool × Bool) : Set M := P.productCoordinates '' P.closedSectorBox i

theorem sectorBox_subset_closed (i : Bool × Bool) : P.sectorBox i ⊆ P.closedSectorBox i :=
  prod_mono (sectorInterval_subset_closed _ _ _) (sectorInterval_subset_closed _ _ _)

theorem closedSectorBox_subset_rectangle (i : Bool × Bool) {q : ℝ × ℝ}
    (hq : q ∈ P.closedSectorBox i) :
    collarParameterEquiv.symm q ∈ crossingClosedRectangle P.center.1 P.center.2 P.width := by
  change collarParameterEquiv (collarParameterEquiv.symm q) ∈ closedBall P.center P.width
  rw [collarParameterEquiv.apply_symm_apply, ← closedBall_prod_same,
    Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]
  exact ⟨closedSectorInterval_subset _ _ _ P.width_pos.le hq.1,
    closedSectorInterval_subset _ _ _ P.width_pos.le hq.2⟩

theorem closedSectorBox_subset_source (i : Bool × Bool) :
    P.closedSectorBox i ⊆ P.productCoordinates.source :=
  fun _ hq => ⟨mem_univ _, P.rectangle_subset (P.closedSectorBox_subset_rectangle i hq)⟩

theorem closedSector_subset_carrier (i : Bool × Bool) : P.closedSector i ⊆ P.carrier := by
  rw [P.carrier_eq_image_rectangle]
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨collarParameterEquiv.symm q, P.closedSectorBox_subset_rectangle i hq, rfl⟩

theorem sector_subset_closed (i : Bool × Bool) : P.sector i ⊆ P.closedSector i :=
  image_mono (P.sectorBox_subset_closed i)

theorem isPathConnected_sector (i : Bool × Bool) : IsPathConnected (P.sector i) :=
  ((sectorInterval_connected _ P.width_pos i.1).prod
    (sectorInterval_connected _ P.width_pos i.2)).image'
      (P.productCoordinates.continuousOn.mono
        ((P.sectorBox_subset_closed i).trans (P.closedSectorBox_subset_source i)))

theorem mem_closedSector (i : Bool × Bool) : p ∈ P.closedSector i := by
  refine ⟨P.center, ⟨center_mem_closedSectorInterval _ P.width_pos.le i.1,
    center_mem_closedSectorInterval _ P.width_pos.le i.2⟩, ?_⟩
  change P.coordinates (collarParameterEquiv.symm P.center) = p
  rw [← P.center_eq]
  exact P.coordinates.right_inv (P.carrier_subset_target
    (P.openCarrier_subset_carrier P.mem_openCarrier))

theorem closedSectors_cover : (⋃ i, P.closedSector i) = P.carrier := by
  apply Subset.antisymm (iUnion_subset P.closedSector_subset_carrier)
  rw [P.carrier_eq_image_rectangle]
  rintro _ ⟨z, hz, rfl⟩
  rw [crossingClosedRectangle_eq] at hz
  obtain ⟨i, hi⟩ := exists_mem_closedSectorInterval hz.1
  obtain ⟨j, hj⟩ := exists_mem_closedSectorInterval hz.2
  refine mem_iUnion.mpr ⟨(i, j), collarParameterEquiv z, ⟨hi, hj⟩, ?_⟩
  change P.coordinates (collarParameterEquiv.symm (collarParameterEquiv z)) = _
  rw [collarParameterEquiv.symm_apply_apply]

theorem sector_disjoint_circles (i : Bool × Bool) : Disjoint (P.sector i) P.circles := by
  apply disjoint_left.mpr
  rintro _ ⟨q, hq, rfl⟩ hcircles
  have hsource := (P.closedSectorBox_subset_source i (P.sectorBox_subset_closed i hq)).2
  have haxes := (P.coordinates_mem_circles_iff hsource).mp hcircles
  have hne₁ := ne_center_of_mem_sectorInterval hq.1
  have hne₂ := ne_center_of_mem_sectorInterval hq.2
  have he : (collarParameterEquiv.symm q) 0 = P.center.1 ∨
      (collarParameterEquiv.symm q) 1 = P.center.2 := by
    cases P with
    | single x Q => exact Or.inl haxes
    | crossing x y hxy Q => exact haxes
  change q.1 = P.center.1 ∨ q.2 = P.center.2 at he
  exact he.elim hne₁ hne₂

variable [T2Space M]

omit [T2Space M] in
theorem isCompact_closedSector (i : Bool × Bool) : IsCompact (P.closedSector i) := by
  have hinterval (c : ℝ) (j : Bool) : IsCompact (closedSectorInterval c P.width j) := by
    cases j <;> exact isCompact_Icc
  exact ((hinterval _ i.1).prod (hinterval _ i.2)).image_of_continuousOn
    (P.productCoordinates.continuousOn.mono (P.closedSectorBox_subset_source i))

theorem closure_sector (i : Bool × Bool) : closure (P.sector i) = P.closedSector i := by
  apply Subset.antisymm
  · exact closure_minimal (P.sector_subset_closed i) (P.isCompact_closedSector i).isClosed
  · rintro _ ⟨q, hq, rfl⟩
    have hqcl : q ∈ closure (P.sectorBox i) := by
      simpa only [sectorBox, closure_prod_eq, closure_sectorInterval _ P.width_pos,
        closedSectorBox] using hq
    exact mem_closure_image
      (P.productCoordinates.continuousAt (P.closedSectorBox_subset_source i hq)) hqcl

end ChartCircleArrangementVertexPatch
end PoincareConjecture.Topology.Surface
