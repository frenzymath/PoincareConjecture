import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.DiskProductHalves

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Cube" => closedBall (0 : V3) 1
local notation "atlas" => (fun _ : Unit => OpenPartialHomeomorph.refl V3)

theorem exists_closed_cube_disk_cut_balls
    {j : V2 → V3} (P : OriginalDiskProduct atlas Cube j)
    (hopen : IsOpen ((Subtype.val : Cube → V3) ⁻¹' P.openStrip))
    (hPL : PLDomain atlas P.cutCarrier) :
    ∃ B r : Bool → Set V3,
      (∀ b, IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B b) (r b)) ∧
      B false ∪ B true = Cube ∧ B false ∩ B true = j '' Disk ∧
      (∀ b, j '' Disk ⊆ r b) ∧
      ∀ b, r b = (B b ∩ sphere (0 : V3) 1) ∪ j '' Disk := by
  classical
  obtain ⟨C,k,_,_,hC,hcover,hdis,hk,hwhole⟩ := P.exists_two_cube_cut_balls hopen hPL
  let H := fun b => P.map '' (Disk ×ˢ halfInterval b)
  let T := fun b => P.map '' halfBoundary b
  have hHstrip (b : Bool) : H b ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl (halfInterval_subset b))
  have hcapH (b : Bool) : P.capDisk b ⊆ H b := image_mono (cap_source_subset_half b)
  have hCH (b : Bool) : C b ∩ H b = P.capDisk b := by
    apply Subset.antisymm
    · exact fun x hx => (hk b).2.2.2.2.2.2.2.1.subset ⟨hx.1,hHstrip b hx.2⟩
    · exact fun x hx => ⟨(hk b).2.2.2.2.2.1 hx,hcapH b hx⟩
  have hCHop (b : Bool) : Disjoint (C b) (H (!b)) := by
    apply disjoint_left.mpr
    intro x hxC hxH
    have hxcap := (hk b).2.2.2.2.2.2.2.1.subset ⟨hxC,hHstrip (!b) hxH⟩
    exact disjoint_left.mp (P.cap_disjoint_opposite_half b) hxcap hxH
  let B := fun b => C b ∪ H b
  let r := fun b => (frontier (C b) \ (P.capDisk b \ P.capRimSet b)) ∪
    (T b \ (P.capDisk b \ P.capRimSet b))
  have hball (b : Bool) : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B b) (r b) := by
    have hcapfront : P.capDisk b ⊆ frontier (C b) := by
      rw [(hk b).2.2.2.1]
      exact subset_union_right
    have hCout : (frontier (C b) \ P.capDisk b).Nonempty := by
      obtain ⟨x,hx,hxr⟩ := (hk b).1.sdiff_nonempty
      refine ⟨x, ?_, ?_⟩
      · rw [(hk b).2.2.2.1]
        exact Or.inl hx
      · intro hcap
        exact hxr ((hk b).2.2.2.2.1.subset ⟨hx,hcap⟩)
    exact (hC b).1.union_of_actual_disk_contact (P.half_image_ball b)
      (P.cap_disk_ball b) hcapfront (P.cap_subset_half_boundary b)
      hCout (P.half_boundary_outside_cap b) (hCH b)
  have hHH : H false ∩ H true = j '' Disk := P.half_images_inter
  have hcentral_miss (b : Bool) : Disjoint (j '' Disk) (P.capDisk b) := by
    apply disjoint_left.mpr
    intro x hx hc
    have hH := hHH.symm.subset hx
    apply disjoint_left.mp (P.cap_disjoint_opposite_half b) hc
    cases b
    · exact hH.2
    · exact hH.1
  have hCS (b : Bool) : C b ∩ sphere (0 : V3) 1 = k b := by
    apply Subset.antisymm
    · rintro x ⟨hxC,hxS⟩
      have hxfront : x ∈ frontier (C b) := by
        refine ⟨subset_closure hxC, ?_⟩
        intro hxint
        have hxcube : x ∈ frontier Cube := by
          rwa [frontier_closedBall _ one_ne_zero]
        exact hxcube.2 (interior_mono (hk b).2.2.2.2.2.2.2.2 hxint)
      rcases (hk b).2.2.2.1.subset hxfront with hxk | hxcap
      · exact hxk
      · apply (hk b).1.1
        apply (P.cap_inter_frontier b).subset
        exact ⟨hxcap,by rwa [frontier_closedBall _ one_ne_zero]⟩
    · intro x hx
      exact ⟨(hk b).2.2.1 hx,(hk b).2.1 hx⟩
  have hrmark (b : Bool) : r b = (B b ∩ sphere (0 : V3) 1) ∪ j '' Disk := by
    change (frontier (C b) \ (P.capDisk b \ P.capRimSet b)) ∪
      ((P.map '' halfBoundary b) \ (P.capDisk b \ P.capRimSet b)) = _
    rw [(hk b).2.2.2.1,P.half_boundary_image_eq,frontier_closedBall _ one_ne_zero]
    change _ = ((C b ∪ H b) ∩ sphere (0 : V3) 1) ∪ j '' Disk
    rw [union_inter_distrib_right,hCS b]
    ext x
    have hkr : x ∈ k b ∩ P.capDisk b ↔ x ∈ P.capRimSet b :=
      (hk b).2.2.2.2.1 ▸ Iff.rfl
    have hHr : x ∈ H b ∩ sphere (0 : V3) 1 → x ∈ P.capDisk b → x ∈ P.capRimSet b := by
      intro hx hc
      apply (P.cap_inter_frontier b).subset
      exact ⟨hc,by simpa only [frontier_closedBall _ one_ne_zero] using hx.2⟩
    have hJr : x ∈ j '' Disk → x ∉ P.capDisk b :=
      fun hx => disjoint_left.mp (hcentral_miss b) hx
    simp only [mem_union,mem_sdiff,mem_inter_iff] at hkr hHr ⊢
    tauto
  refine ⟨B,r,hball,?_,?_,?_,hrmark⟩
  · change (C false ∪ H false) ∪ (C true ∪ H true) = Cube
    calc
      _ = (H false ∪ H true) ∪ (C false ∪ C true) := by ac_rfl
      _ = Cube := by rw [P.half_images_union]; exact hwhole
  · ext x
    change (x ∈ C false ∪ H false ∧ x ∈ C true ∪ H true) ↔ x ∈ j '' Disk
    rw [← hHH]
    constructor
    · rintro ⟨h0,h1⟩
      rcases h0 with hC0 | hH0
      · rcases h1 with hC1 | hH1
        · exact (disjoint_left.mp hdis hC0 hC1).elim
        · exact (disjoint_left.mp (hCHop false) hC0 hH1).elim
      · rcases h1 with hC1 | hH1
        · exact (disjoint_left.mp (hCHop true) hC1 hH0).elim
        · exact ⟨hH0,hH1⟩
    · intro h
      exact ⟨Or.inr h.1,Or.inr h.2⟩
  · intro b x hx
    have hxH : x ∈ H (!b) := by
      have hh := hHH.symm.subset hx
      cases b
      · exact hh.2
      · exact hh.1
    have hxcap : x ∉ P.capDisk b := fun h =>
      disjoint_left.mp (P.cap_disjoint_opposite_half b) h hxH
    apply Or.inr
    refine ⟨?_, fun h => hxcap h.1⟩
    obtain ⟨z,hz,rfl⟩ := hx
    refine ⟨(z,0),Or.inr ⟨hz,?_⟩,P.central z hz⟩
    cases b <;> simp

end PoincareConjecture.M76.OriginalDiskProduct
