import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedBoundaryLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskComponentProduct









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem selected_sphere_subset_parent_component
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R B : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hB : IsConnected B) (hBR : B ⊆ R)
    (hband : P.map '' (Rim ×ˢ J) ⊆ B) {a : X} (ha : a ∈ P.capDisk false) :
    B ⊆ connectedComponentIn R a := by
  let M := P.map '' (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1)
  have hM : IsConnected M :=
    ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))).image _ P.polyhedral.continuousOn
  have hMR : M ⊆ R := by
    rintro _ ⟨z, hz, rfl⟩
    exact P.inside hz
  have haM : a ∈ M := image_mono (cap_source_subset false) ha
  have hMC := hM.isPreconnected.subset_connectedComponentIn haM hMR
  obtain ⟨z, hz⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
  have hpointB : P.map (z, 0) ∈ B := hband ⟨(z, 0), ⟨hz, by norm_num⟩, rfl⟩
  have hpointC : P.map (z, 0) ∈ connectedComponentIn R a :=
    hMC ⟨(z, 0), ⟨sphere_subset_closedBall hz, by norm_num⟩, rfl⟩
  rw [connectedComponentIn_eq hpointC]
  exact hB.isPreconnected.subset_connectedComponentIn hpointB hBR

theorem replacement_boundary_labels
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (S : κ → Set X) (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier R = ⋃ i, S i) (i : κ)
    (hband : P.map '' (Rim ×ˢ J) ⊆ S i)
    (ret : Bool → Set X)
    (hret : S i \ P.openStrip = ret false ∪ ret true)
    (hnewdis : Disjoint (ret false ∪ P.capDisk false) (ret true ∪ P.capDisk true))
    (hcutfront : frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks) :
    let T : {j : κ // j ≠ i} ⊕ Bool → Set X :=
      Sum.elim (fun j => S j) (fun b => ret b ∪ P.capDisk b)
    (∀ j, j ≠ i → Disjoint (S j) P.closedStrip) ∧
      Pairwise (fun j k => Disjoint (T j) (T k)) ∧
      frontier P.cutCarrier = ⋃ j, T j := by
  classical
  let T : {j : κ // j ≠ i} ⊕ Bool → Set X :=
    Sum.elim (fun j => S j) (fun b => ret b ∪ P.capDisk b)
  have hother (l : κ) (hli : l ≠ i) : Disjoint (S l) P.closedStrip := by
    apply disjoint_left.mpr
    rintro x hx ⟨z, hz, hzx⟩
    have hzfull : z ∈ closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    have hxfront : x ∈ frontier R := hfront.symm.subset (mem_iUnion.mpr ⟨l, hx⟩)
    have hzrim : z.1 ∈ Rim := (P.proper z hzfull).mp (hzx.symm ▸ hxfront)
    exact disjoint_left.mp (hSdis hli) hx (hband ⟨z, ⟨hzrim, hz.2⟩, hzx⟩)
  have hretsub (b : Bool) : ret b ⊆ S i := by
    intro x hx
    apply (hret.symm.subset ?_).1
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hcapsub (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hcross (l : {j : κ // j ≠ i}) (b : Bool) :
      Disjoint (S l) (ret b ∪ P.capDisk b) :=
    ((hSdis l.property).mono_right (hretsub b)).union_right
      ((hother l l.property).mono_right (hcapsub b))
  refine ⟨hother, ?_, ?_⟩
  · intro l m hlm
    cases l with
    | inl l =>
      cases m with
      | inl m => exact hSdis (fun h => hlm (congrArg Sum.inl (Subtype.ext h)))
      | inr b => exact hcross l b
    | inr b =>
      cases m with
      | inl l => exact (hcross l b).symm
      | inr c =>
        cases b <;> cases c
        · exact False.elim (hlm rfl)
        · exact hnewdis
        · exact hnewdis.symm
        · exact False.elim (hlm rfl)
  · rw [hcutfront, hfront, P.endDisks_eq_capDisks]
    apply Subset.antisymm
    · rintro x (⟨hx, hxo⟩ | hx | hx)
      · obtain ⟨l, hl⟩ := mem_iUnion.mp hx
        by_cases hli : l = i
        · rcases hret.subset ⟨hli ▸ hl, hxo⟩ with h | h
          · exact mem_iUnion.mpr ⟨Sum.inr false, Or.inl h⟩
          · exact mem_iUnion.mpr ⟨Sum.inr true, Or.inl h⟩
        · exact mem_iUnion.mpr ⟨Sum.inl ⟨l, hli⟩, hl⟩
      · exact mem_iUnion.mpr ⟨Sum.inr false, Or.inr hx⟩
      · exact mem_iUnion.mpr ⟨Sum.inr true, Or.inr hx⟩
    · intro x hx
      obtain ⟨l, hl⟩ := mem_iUnion.mp hx
      cases l with
      | inl l =>
        exact Or.inl ⟨mem_iUnion.mpr ⟨l, hl⟩, fun ho =>
          disjoint_left.mp (hother l l.property) hl
            (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) ho)⟩
      | inr b =>
        rcases hl with hr | hc
        · have hr' : x ∈ S i \ P.openStrip := hret.symm.subset (by
            cases b
            · exact Or.inl hr
            · exact Or.inr hr)
          exact Or.inl ⟨mem_iUnion.mpr ⟨i, hr'.1⟩, hr'.2⟩
        · apply Or.inr
          cases b
          · exact Or.inl hc
          · exact Or.inr hc

end PoincareConjecture.M76.OriginalDiskProduct
