import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.OriginalStripClosure
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.ProductStripCutTopology

/-!
# The complete physical cut of the original disk product

The actual half-width cut retains the entire unremoved old frontier
and both complete endpoint disks. Its original ambient interior has
an explicit point. See Hamilton1976 p.67 and rigidity036.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

namespace OriginalDiskProduct

/-- The complete closed strip at half the constructed width. -/
def closedStrip (P : OriginalDiskProduct e R j) : Set X :=
  P.map '' (D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2))

/-- The whole R-open middle, including its entire lateral band. -/
def openStrip (P : OriginalDiskProduct e R j) : Set X :=
  P.map '' (D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))

/-- Both complete end disks with their unchanged parameters. -/
def endDisks (P : OriginalDiskProduct e R j) : Set X :=
  P.map '' (D ×ˢ ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ))

/-- The literal closed cut carrier in the original region. -/
def cutCarrier (P : OriginalDiskProduct e R j) : Set X := R \ P.openStrip

/-- Removing the entire open middle from the entire closed strip
leaves exactly the two end disks. See rigidity036, section3. -/
theorem closedStrip_sdiff_openStrip (P : OriginalDiskProduct e R j) :
    P.closedStrip \ P.openStrip = P.endDisks := by
  have hfull : D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2) ⊆ D ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hnot⟩
    refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
    have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
      by_contra hn
      push Not at hn
      exact hnot ⟨z, ⟨hz.1, lt_of_le_of_ne hz.2.1 (Ne.symm hn.1),
        lt_of_le_of_ne hz.2.2 hn.2⟩, rfl⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using ht
  · rintro ⟨z, hz, rfl⟩
    have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hz.2
    have hzsmall : z ∈ D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      refine ⟨hz.1, ?_⟩
      rcases ht with ht | ht <;> rw [ht] <;> norm_num
    refine ⟨⟨z, hzsmall, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    have heq := P.injective (hfull ⟨hw.1, Ioo_subset_Icc_self hw.2⟩)
      (hfull hzsmall) hwz
    subst w
    rcases ht with ht | ht <;> linarith [hw.2.1, hw.2.2]

/-- The actual cut has its complete frontier, complete overlap and
cover, compactness and an original ambient interior point. No ball or
connectedness conclusion is assumed. See rigidity036, sections3--4. -/
theorem cut_geometry [T2Space X] (P : OriginalDiskProduct e R j)
    (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    IsCompact P.cutCarrier ∧
      interior P.cutCarrier = interior R \ P.closedStrip ∧
      frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks ∧
      P.closedStrip ∩ P.cutCarrier = P.endDisks ∧
      P.closedStrip ∪ P.cutCarrier = R ∧
      (interior P.cutCarrier).Nonempty := by
  have hfull : D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2) ⊆ D ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hCR : P.closedStrip ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact P.inside (hfull hz)
  have hUC : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hCU : interior P.closedStrip ⊆ P.openStrip := by
    change interior (P.map '' (D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2))) ⊆ _
    rw [P.interior_closed_strip (by norm_num : (1 / 2 : ℝ) < 1) hopen]
    exact image_mono (prod_mono ball_subset_closedBall subset_rfl)
  have hC : IsClosed P.closedStrip := (P.isCompact_closed_strip
    (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  have hCdense : closure (interior P.closedStrip) = P.closedStrip :=
    P.closure_interior_closed_strip (by norm_num) (by norm_num) hopen
  obtain ⟨hclosed, hint, hfront, hoverlap, hcover⟩ :=
    physical_strip_cut_geometry hR.isClosed hC hCR hUC hCU hCdense hopen
      P.closedStrip_sdiff_openStrip
  refine ⟨hR.of_isClosed_subset hclosed sdiff_subset, hint, hfront, hoverlap, hcover, ?_⟩
  change (interior (R \ P.openStrip)).Nonempty
  rw [hint]
  let z : V2 × ℝ := (0, 3 / 4)
  have hz : z ∈ D ×ˢ I := ⟨mem_closedBall_self zero_le_one, by norm_num [z]⟩
  have hzR : P.map z ∈ interior R := by
    apply (mem_interior_iff_notMem_frontier (P.inside hz)).mpr
    intro h
    have hq := (P.proper z hz).mp h
    norm_num [z, mem_sphere_zero_iff_norm] at hq
  refine ⟨P.map z, hzR, ?_⟩
  rintro ⟨w, hw, hwz⟩
  have ht := congrArg Prod.snd (P.injective (hfull hw) hz hwz)
  change w.2 = 3 / 4 at ht
  linarith [hw.2.2]

/-- The two whole cap images remain disjoint. See rigidity036. -/
theorem disjoint_end_disks (P : OriginalDiskProduct e R j) :
    Disjoint (P.map '' (D ×ˢ ({-(1 / 2 : ℝ)} : Set ℝ)))
      (P.map '' (D ×ˢ ({1 / 2} : Set ℝ))) := by
  apply disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
  have hzt : z.2 = -(1 / 2 : ℝ) := hz.2
  have hwt : w.2 = (1 / 2 : ℝ) := hw.2
  have hzI : z ∈ D ×ˢ I := ⟨hz.1, by rw [hzt]; norm_num⟩
  have hwI : w ∈ D ×ˢ I := ⟨hw.1, by rw [hwt]; norm_num⟩
  have ht := congrArg Prod.snd (P.injective hwI hzI hwz)
  linarith

/-- The complete original central disk is removed by the cut. See036. -/
theorem disjoint_central_cut (P : OriginalDiskProduct e R j) :
    Disjoint (j '' D) P.cutCarrier := by
  apply disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ hx
  apply hx.2
  exact ⟨(z, 0), ⟨hz, by norm_num⟩, P.central z hz⟩

end OriginalDiskProduct
end PoincareMT.M76
