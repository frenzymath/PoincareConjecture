import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.CompactCapComplement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Analysis.Normed.Module.Connected











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

variable {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}

namespace SurgeryCapTag


def sourceCapInterior (C : SurgeryCapTag ψ u) : Set UnitTwoSphere :=
  C.sourceChart '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 < 0}



theorem sourceCapInterior_isOpen (C : SurgeryCapTag ψ u) :
    IsOpen C.sourceCapInterior := by
  change IsOpen (C.sourceChart ''
    {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 < 0})
  apply C.sourceChart.isOpen_image_of_subset_source
  · exact isOpen_lt
      ((heightCoordinates.continuous.comp continuous_subtype_val).snd) continuous_const
  · intro q hq
    exact C.south_mem_source q hq.le


theorem sourceCapInterior_subset (C : SurgeryCapTag ψ u) :
    C.sourceCapInterior ⊆ C.sourceCap := by
  rintro p ⟨q, hq, rfl⟩
  change (heightCoordinates (q : E3)).2 < 0 at hq
  exact ⟨q, hq.le, rfl⟩


theorem sourceCap_diff_interior (C : SurgeryCapTag ψ u) :
    C.sourceCap \ C.sourceCapInterior = C.sourceSeam := by
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hnot⟩
    refine ⟨q, le_antisymm hq (le_of_not_gt ?_), rfl⟩
    intro hneg
    exact hnot ⟨q, hneg, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, hq.le, rfl⟩, ?_⟩
    rintro ⟨q', hq', heq⟩
    have hqq : q' = q := C.sourceChart.injOn
      (C.south_mem_source q' hq'.le) (C.south_mem_source q hq.le) heq
    subst q'
    exact (not_lt_of_ge hq.ge) hq'


theorem sourceCap_isConnected (C : SurgeryCapTag ψ u) :
    IsConnected C.sourceCap := by
  have hnorth : IsConnected
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} := by
    rw [← northSpherePoint_image_closedBall]
    exact (isConnected_closedBall (x := (0 : E2)) (r := (1 : ℝ)) (by norm_num)).image
      northSpherePoint northSpherePoint_contMDiff.continuous.continuousOn
  have hheight (q : UnitTwoSphere) :
      (heightCoordinates ((-q : UnitTwoSphere) : E3)).2 =
        -(heightCoordinates (q : E3)).2 := by
    change (heightCoordinates (-(q : E3))).2 = -(heightCoordinates (q : E3)).2
    exact congrArg Prod.snd (map_neg heightCoordinates (q : E3))
  have hneg : (fun q : UnitTwoSphere => -q) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      change (heightCoordinates ((-p : UnitTwoSphere) : E3)).2 ≤ 0
      rw [hheight]
      exact neg_nonpos.mpr hp
    · intro hq
      refine ⟨-q, ?_, neg_neg q⟩
      change 0 ≤ (heightCoordinates ((-q : UnitTwoSphere) : E3)).2
      rw [hheight]
      exact neg_nonneg.mpr hq
  have hsouth : IsConnected
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    rw [← hneg]
    exact hnorth.image (fun q : UnitTwoSphere => -q)
      (continuous_neg : Continuous (fun q : UnitTwoSphere => -q)).continuousOn
  exact hsouth.image C.sourceChart
    (C.sourceChart.continuousOn.mono (fun q hq => C.south_mem_source q hq))


theorem sourceSeam_isConnected (C : SurgeryCapTag ψ u) :
    IsConnected C.sourceSeam := by
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  have hcircle : IsConnected (sphere (0 : E2) 1) :=
    isConnected_sphere hdim (0 : E2) (by norm_num)
  have heq : northSpherePoint '' sphere (0 : E2) 1 =
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact congrArg Prod.snd (northSpherePoint_equator (⟨x, hx⟩ : UnitCircle))
    · intro hq
      have hnorm : ‖(heightCoordinates (q : E3)).1‖ = 1 := by
        have hsq := sphere_height_coordinates_sq q
        rw [hq] at hsq
        nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
      have hx : (heightCoordinates (q : E3)).1 ∈ sphere (0 : E2) 1 :=
        mem_sphere_zero_iff_norm.mpr hnorm
      refine ⟨(heightCoordinates (q : E3)).1, hx, ?_⟩
      apply Subtype.ext
      apply heightCoordinates.injective
      have hcoords := northSpherePoint_equator
        (⟨(heightCoordinates (q : E3)).1, hx⟩ : UnitCircle)
      exact hcoords.trans (Prod.ext rfl hq.symm)
  have hequator : IsConnected
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} := by
    rw [← heq]
    exact hcircle.image northSpherePoint northSpherePoint_contMDiff.continuous.continuousOn
  exact hequator.image C.sourceChart
    (C.sourceChart.continuousOn.mono (fun q hq => C.south_mem_source q hq.le))

end SurgeryCapTag



theorem tagged_source_complement_compact_connected
    {ι : Type*} (s : Finset ι) (C : ι → SurgeryCapTag ψ u)
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i).cap (C j).cap) :
    IsCompact ((univ : Set UnitTwoSphere) \ ⋃ i ∈ s, (C i).sourceCapInterior) ∧
      IsConnected ((univ : Set UnitTwoSphere) \ ⋃ i ∈ s, (C i).sourceCapInterior) ∧
      ∀ i ∈ s, (C i).sourceCap ∩
        ((univ : Set UnitTwoSphere) \ ⋃ j ∈ s, (C j).sourceCapInterior) =
          (C i).sourceSeam := by
  have hdim : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  have hconnected : IsConnected (univ : Set UnitTwoSphere) := by
    let : ConnectedSpace UnitTwoSphere :=
      Subtype.connectedSpace (isConnected_sphere hdim (0 : E3) (by norm_num))
    exact isConnected_univ
  have hsource : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (C i).sourceCap (C j).sourceCap := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro q hqi hqj
    exact disjoint_left.mp (hdisjoint i hi j hj hij)
      (show ψ (q, 0) ∈ (C i).cap from ⟨q, hqi, rfl⟩)
      (show ψ (q, 0) ∈ (C j).cap from ⟨q, hqj, rfl⟩)
  obtain ⟨hc, hn, hs⟩ := compact_connected_diff_finite_caps
    (univ : Set UnitTwoSphere) s (fun i => (C i).sourceCap)
    (fun i => (C i).sourceCapInterior) isCompact_univ hconnected
    (fun i _ => (C i).sourceCap_isCompact)
    (fun _ _ => subset_univ _)
    (fun i _ => (C i).sourceCapInterior_isOpen)
    (fun i _ => (C i).sourceCapInterior_subset)
    (fun i _ => by
      rw [(C i).sourceCap_diff_interior]
      exact (C i).sourceSeam_isConnected) hsource
  refine ⟨hc, hn, ?_⟩
  intro i hi
  exact (hs i hi).trans (C i).sourceCap_diff_interior



theorem tagged_retained_core_compact_connected
    (hψ : IsCollarEmbedding ψ)
    {ι : Type*} (s : Finset ι) (C : ι → SurgeryCapTag ψ u)
    (hdisjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i).cap (C j).cap)
    (L : Set E3)
    (hcover : range (fun q : UnitTwoSphere => ψ (q, 0)) =
      L ∪ ⋃ i ∈ s, (C i).cap)
    (hinter : ∀ i ∈ s, L ∩ (C i).cap = (C i).seam) :
    L = (fun q : UnitTwoSphere => ψ (q, 0)) ''
      ((univ : Set UnitTwoSphere) \ ⋃ i ∈ s, (C i).sourceCapInterior) ∧
      IsCompact L ∧ IsConnected L := by
  have hdim : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  have hconnected : IsConnected (univ : Set UnitTwoSphere) := by
    let : ConnectedSpace UnitTwoSphere :=
      Subtype.connectedSpace (isConnected_sphere hdim (0 : E3) (by norm_num))
    exact isConnected_univ
  have hsource : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (C i).sourceCap (C j).sourceCap := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro q hqi hqj
    exact disjoint_left.mp (hdisjoint i hi j hj hij)
      (show ψ (q, 0) ∈ (C i).cap from ⟨q, hqi, rfl⟩)
      (show ψ (q, 0) ∈ (C j).cap from ⟨q, hqj, rfl⟩)
  have hinj : Function.Injective (fun q : UnitTwoSphere => ψ (q, 0)) := by
    intro q q' heq
    exact congrArg Prod.fst (hψ.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ heq)
  have hcontinuous : ContinuousOn (fun q : UnitTwoSphere => ψ (q, 0)) univ :=
    (collar_central_contMDiff ψ hψ).continuous.continuousOn
  refine compact_connected_retained_of_cap_cover
    (univ : Set UnitTwoSphere) s (fun i => (C i).sourceCap)
    (fun i => (C i).sourceCapInterior) isCompact_univ hconnected
    (fun i _ => (C i).sourceCap_isCompact)
    (fun _ _ => subset_univ _)
    (fun i _ => (C i).sourceCapInterior_isOpen)
    (fun i _ => (C i).sourceCapInterior_subset)
    (fun i _ => by
      rw [(C i).sourceCap_diff_interior]
      exact (C i).sourceSeam_isConnected) hsource
    (fun q : UnitTwoSphere => ψ (q, 0)) hinj hcontinuous L ?_ ?_
  · simpa only [image_univ, SurgeryCapTag.cap] using hcover
  · intro i hi
    simpa only [SurgeryCapTag.cap, SurgeryCapTag.seam,
      (C i).sourceCap_diff_interior] using hinter i hi

end PoincareConjecture.M25.Topology3D
