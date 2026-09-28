import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoAttachedDiskComplements












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)




theorem middle_strip_disk_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M QM Q : Set E} (hM : IsFinitePLBallPair P2 M QM)
    (c : Bool → P2 → E) (positive : Bool → Bool)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hhalfM : ∀ i, c i '' halfSource (positive i) ⊆ M)
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hQM : QM = ((M ∩ Q) ∪ c false '' arm 0) ∪ c true '' arm 0) :
    let H := fun i => c i '' halfSource (positive i)
    let W := fun i => c i '' arm (farArmParameter (positive i))
    let C := M \ ((H false \ W false) ∪ (H true \ W true))
    IsFinitePLBallPair P2 C (((C ∩ Q) ∪ W false) ∪ W true) ∧
      (H false ∪ H true) ∪ C = M ∧
      (∀ i, H i ∩ C = W i) ∧
      (∀ i, IsFinitePLBallPair ℝ (W i)
        {c i (0, farArmParameter (positive i)), c i (1, farArmParameter (positive i))}) ∧
      Disjoint C ((c false '' arm 0) ∪ (c true '' arm 0)) := by
  let H := fun i => c i '' halfSource (positive i)
  let W := fun i => c i '' arm (farArmParameter (positive i))
  let C := M \ ((H false \ W false) ∪ (H true \ W true))
  have hcenterS : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  have hcenterM (i : Bool) : c i '' arm 0 ⊆ M :=
    (image_mono (arm_zero_subset_halfSource (positive i))).trans (hhalfM i)
  have hdisjOther (i : Bool) : Disjoint (c i '' source) (c (!i) '' source) := by
    cases i
    · exact hdisj
    · exact hdisj.symm
  have hQaug (i : Bool) (x : P2) (hx : x ∈ source) :
      c i x ∈ Q ∪ c (!i) '' arm 0 ↔ x.1 = 0 ∨ x.1 = 1 := by
    constructor
    · rintro (hxQ | hxC)
      · exact (hcQ i x hx).mp hxQ
      · exact False.elim (Set.disjoint_left.mp (hdisjOther i)
          (mem_image_of_mem (c i) hx) ((image_mono hcenterS) hxC))
    · exact fun h => Or.inl ((hcQ i x hx).mpr h)
  have hQA (i : Bool) : QM = (M ∩ (Q ∪ c (!i) '' arm 0)) ∪ c i '' arm 0 := by
    rw [hQM]
    cases i <;> ext x <;>
      have h0 := hcenterM false (a := x) <;>
      have h1 := hcenterM true (a := x) <;>
      simp only [Bool.not_false, Bool.not_true, mem_union, mem_inter_iff] <;> tauto
  choose U hH hU hUQM hW hab hproper using fun i =>
    exists_half_strip_attaching_arc (c i) (positive i) (hcPL i) (hci i)
      (hQaug i) (hhalfM i) (hQA i)
  have hdisjH : Disjoint (H false) (H true) := hdisj.mono
    (image_mono (halfSource_subset_source (positive false)))
    (image_mono (halfSource_subset_source (positive true)))
  obtain ⟨hC, hcover, hcontact⟩ := two_boundary_attached_disks_complement hM H U W
    (fun i => c i (0, farArmParameter (positive i)))
    (fun i => c i (1, farArmParameter (positive i)))
    hH hhalfM hU hUQM hW hab hproper hdisjH
  have hcenterFar (i : Bool) : Disjoint (c i '' arm 0) (W i) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyfar : y.2 = farArmParameter (positive i) := hy.2
    have hyS : y ∈ source := by
      refine ⟨hy.1, ?_⟩
      rw [hyfar]
      cases positive i <;> norm_num [farArmParameter]
    have heq := hci i hyS (hcenterS hx) hyx
    have hx0 : x.2 = 0 := hx.2
    exact farArmParameter_ne_zero (positive i)
      (hyfar.symm.trans ((congrArg Prod.snd heq).trans hx0))
  have hnoCenter (i : Bool) : Disjoint C (c i '' arm 0) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxcenter
    have hxH : x ∈ H i := (image_mono (arm_zero_subset_halfSource (positive i))) hxcenter
    exact Set.disjoint_left.mp (hcenterFar i) hxcenter
      ((hcontact i).subset ⟨hxH, hxC⟩)
  have hCQ : C ∩ QM = C ∩ Q := by
    rw [hQM]
    ext x
    constructor
    · rintro ⟨hxC, (⟨_, hxQ⟩ | hx0) | hx1⟩
      · exact ⟨hxC, hxQ⟩
      · exact False.elim (Set.disjoint_left.mp (hnoCenter false) hxC hx0)
      · exact False.elim (Set.disjoint_left.mp (hnoCenter true) hxC hx1)
    · rintro ⟨hxC, hxQ⟩
      exact ⟨hxC, Or.inl (Or.inl ⟨hxC.1, hxQ⟩)⟩
  rw [hCQ] at hC
  refine ⟨hC, hcover, hcontact, hW, ?_⟩
  exact Set.disjoint_union_right.mpr ⟨hnoCenter false, hnoCenter true⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
