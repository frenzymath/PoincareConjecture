import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripCutDecomposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MiddleStripDiskComplement











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

private theorem whole_strip_contact
    {E : Type*} {H K B A T Z F L : Set E}
    (hcover : H ∪ K = L) (hKB : K ⊆ B) (hTA : T ⊆ A)
    (hAB : A ∩ B = Z) (hTZ : Disjoint T Z) (hHT : H ∩ T = F) : L ∩ T = F := by
  apply Subset.antisymm
  · rintro x ⟨hxL, hxT⟩
    rcases hcover.symm.subset hxL with hxH | hxK
    · exact hHT.subset ⟨hxH, hxT⟩
    · exact False.elim (Set.disjoint_left.mp hTZ hxT (hAB.subset ⟨hTA hxT, hKB hxK⟩))
  · intro x hxF
    obtain ⟨hxH, hxT⟩ := hHT.symm.subset hxF
    exact ⟨hcover.subset (Or.inl hxH), hxT⟩




theorem exists_strip_exterior_disks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q) (c : Bool → P2 → E)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source)) :
    ∃ (A M C : Set E) (s0 s1 : Bool),
      IsFinitePLBallPair P2 A ((A ∩ Q) ∪ c false '' arm (farArmParameter (!s0))) ∧
      IsFinitePLBallPair P2 M
        (((M ∩ Q) ∪ c false '' arm (farArmParameter s0)) ∪
          c true '' arm (farArmParameter s1)) ∧
      IsFinitePLBallPair P2 C ((C ∩ Q) ∪ c true '' arm (farArmParameter (!s1))) ∧
      Disjoint A M ∧ Disjoint M C ∧ Disjoint A C ∧
      ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S ∧
      (c false '' source) ∩ A = c false '' arm (farArmParameter (!s0)) ∧
      (c false '' source) ∩ M = c false '' arm (farArmParameter s0) ∧
      (c true '' source) ∩ M = c true '' arm (farArmParameter s1) ∧
      (c true '' source) ∩ C = c true '' arm (farArmParameter (!s1)) ∧
      Disjoint A (c true '' source) ∧ Disjoint C (c false '' source) := by
  obtain ⟨A0, M0, C0, s0, s1, hA0, hM0, hC0, hcover0, hAM0, hMC0, hAC0,
      h0middle, h0outer, h1middle, h1outer⟩ :=
    exists_strip_cut_decomposition hS (c false) (c true) (hcPL false) (hcPL true)
      (hci false) (hci true) (hcS false) (hcS true) (hcQ false) (hcQ true) hdisj
  let positive : Bool → Bool := fun i => if i then s1 else s0
  let H := fun i => c i '' halfSource (positive i)
  let W := fun i => c i '' arm (farArmParameter (positive i))
  let L0 := c false '' halfSource (!s0)
  let L1 := c true '' halfSource (!s1)
  let F0 := c false '' arm (farArmParameter (!s0))
  let F1 := c true '' arm (farArmParameter (!s1))
  let A := A0 \ (L0 \ F0)
  let M := M0 \ ((H false \ W false) ∪ (H true \ W true))
  let C := C0 \ (L1 \ F1)
  obtain ⟨hA, hAcover, hAcontact, hAnoCenter, _⟩ :=
    half_strip_disk_complement hA0 (c false) (!s0) (hcPL false) (hci false)
      (hcQ false) h0outer rfl
  obtain ⟨hC, hCcover, hCcontact, hCnoCenter, _⟩ :=
    half_strip_disk_complement hC0 (c true) (!s1) (hcPL true) (hci true)
      (hcQ true) h1outer rfl
  have hhalfM (i : Bool) : c i '' halfSource (positive i) ⊆ M0 := by
    cases i
    · exact h0middle
    · exact h1middle
  obtain ⟨hM, hMcover, hMcontact, _, hMnoCenter⟩ :=
    middle_strip_disk_complement hM0 c positive hcPL hci hcQ hhalfM hdisj rfl
  have hAA0 : A ⊆ A0 := sdiff_subset
  have hMM0 : M ⊆ M0 := sdiff_subset
  have hCC0 : C ⊆ C0 := sdiff_subset
  have hMno0 : Disjoint M (c false '' arm 0) :=
    hMnoCenter.mono Subset.rfl subset_union_left
  have hMno1 : Disjoint M (c true '' arm 0) :=
    hMnoCenter.mono Subset.rfl subset_union_right
  have hAM : Disjoint A M := by
    apply Set.disjoint_left.mpr
    intro x hxA hxM
    exact Set.disjoint_left.mp hAnoCenter hxA (hAM0.subset ⟨hAA0 hxA, hMM0 hxM⟩)
  have hMC : Disjoint M C := by
    apply Set.disjoint_left.mpr
    intro x hxM hxC
    exact Set.disjoint_left.mp hCnoCenter hxC (hMC0.subset ⟨hMM0 hxM, hCC0 hxC⟩)
  have hAC : Disjoint A C := hAC0.mono hAA0 hCC0
  have hstrip0 : H false ∪ L0 = c false '' source := by
    change (c false '' halfSource s0) ∪ (c false '' halfSource (!s0)) = _
    rw [← image_union, halfSource_union]
  have hstrip1 : H true ∪ L1 = c true '' source := by
    change (c true '' halfSource s1) ∪ (c true '' halfSource (!s1)) = _
    rw [← image_union, halfSource_union]
  have hcover : ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S := by
    change L0 ∪ A = A0 at hAcover
    change (H false ∪ H true) ∪ M = M0 at hMcover
    change L1 ∪ C = C0 at hCcover
    rw [← hstrip0, ← hstrip1]
    calc
      _ = ((L0 ∪ A) ∪ ((H false ∪ H true) ∪ M)) ∪ (L1 ∪ C) := by ac_rfl
      _ = S := by rw [hAcover, hMcover, hCcover, hcover0]
  have h0A : (c false '' source) ∩ A = F0 :=
    whole_strip_contact (by rwa [union_comm]) h0middle hAA0 hAM0 hAnoCenter hAcontact
  have h0M : (c false '' source) ∩ M = W false :=
    whole_strip_contact hstrip0 h0outer hMM0 (by rwa [inter_comm]) hMno0 (hMcontact false)
  have h1M : (c true '' source) ∩ M = W true :=
    whole_strip_contact hstrip1 h1outer hMM0 hMC0 hMno1 (hMcontact true)
  have h1C : (c true '' source) ∩ C = F1 :=
    whole_strip_contact (by rwa [union_comm]) h1middle hCC0
      (by rwa [inter_comm]) hCnoCenter hCcontact
  have hAstrip1 : Disjoint A (c true '' source) := by
    apply Set.disjoint_left.mpr
    intro x hxA hxstrip
    rcases hstrip1.symm.subset hxstrip with hxH | hxL
    · exact Set.disjoint_left.mp hAnoCenter hxA (hAM0.subset ⟨hAA0 hxA, h1middle hxH⟩)
    · exact Set.disjoint_left.mp hAC0 (hAA0 hxA) (h1outer hxL)
  have hCstrip0 : Disjoint C (c false '' source) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxstrip
    rcases hstrip0.symm.subset hxstrip with hxH | hxL
    · exact Set.disjoint_left.mp hCnoCenter hxC (hMC0.subset ⟨h0middle hxH, hCC0 hxC⟩)
    · exact Set.disjoint_left.mp hAC0 (h0outer hxL) (hCC0 hxC)
  exact ⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hAstrip1, hCstrip0⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
