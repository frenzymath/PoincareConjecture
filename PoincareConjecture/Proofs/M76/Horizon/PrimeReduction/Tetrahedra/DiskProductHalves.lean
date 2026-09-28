import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalCubeDiskCutBalls
import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76.OriginalDiskProduct
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Half" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "atlas" => (fun _ : Unit => OpenPartialHomeomorph.refl V3)

def halfInterval (b : Bool) : Set ℝ :=
  Icc (if b then 0 else -(1 / 2)) (if b then 1 / 2 else 0)

def halfBoundary (b : Bool) : Set (V2 × ℝ) :=
  (Rim ×ˢ halfInterval b) ∪
    (Disk ×ˢ {if b then (0 : ℝ) else -(1 / 2), if b then (1 / 2 : ℝ) else 0})

theorem halfInterval_subset (b : Bool) : halfInterval b ⊆ Half := by
  cases b <;> intro t ht <;> simp only [halfInterval, Bool.false_eq_true, ↓reduceIte,
    mem_Icc] at ht ⊢ <;> constructor <;> linarith [ht.1, ht.2]

theorem half_source_subset (b : Bool) : Disk ×ˢ halfInterval b ⊆ Disk ×ˢ I := by
  intro z hz
  have ht := halfInterval_subset b hz.2
  exact ⟨hz.1, by constructor <;> linarith [ht.1, ht.2]⟩

theorem cap_source_subset_half (b : Bool) :
    Disk ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)} ⊆ Disk ×ˢ halfInterval b := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  rw [show z.2 = (if b then (1 / 2 : ℝ) else -(1 / 2)) from hz.2]
  cases b <;> norm_num [halfInterval]

private theorem standard_disk_pair : IsFinitePLBallPair (ℝ × ℝ) Disk Rim := by
  have h := _root_.Dehn.isFinitePLBallPair_annulusSquare
    (L := 8) (u := 0) (by norm_num)
  obtain ⟨e, he, heb⟩ := h.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  apply h.of_homeomorph sphere_subset_closedBall e.symm he.symm
  intro x
  have hx := heb (e.symm x)
  rw [e.apply_symm_apply, frontier_closedBall _ one_ne_zero] at hx
  exact hx.symm

theorem half_source_ball (b : Bool) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (Disk ×ˢ halfInterval b) (halfBoundary b) := by
  exact standard_disk_pair.prod (isFinitePLBallPair_Icc (by cases b <;> norm_num))

theorem half_source_boundary_subset (b : Bool) : halfBoundary b ⊆ Disk ×ˢ halfInterval b :=
  (half_source_ball b).1

variable {R : Set V3} {j : V2 → V3} (P : OriginalDiskProduct atlas R j)

theorem cap_disk_ball (b : Bool) :
    IsFinitePLBallPair (ℝ × ℝ) (P.capDisk b) (P.capRimSet b) :=
  (standard_disk_pair.prod_singleton (if b then (1 / 2 : ℝ) else -(1 / 2))).image_of_subset
    P.finitePiecewiseAffineOn_standard (cap_source_subset b) P.injective

theorem half_image_ball (b : Bool) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (P.map '' (Disk ×ˢ halfInterval b)) (P.map '' halfBoundary b) :=
  (half_source_ball b).image_of_subset P.finitePiecewiseAffineOn_standard
    (half_source_subset b) P.injective

theorem half_images_union :
    (P.map '' (Disk ×ˢ halfInterval false)) ∪
      (P.map '' (Disk ×ˢ halfInterval true)) = P.closedStrip := by
  rw [← image_union, ← prod_union]
  congr 2
  ext t
  simp only [halfInterval, Bool.false_eq_true, ↓reduceIte, mem_union, mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
  · intro h
    by_cases ht : t ≤ 0
    · exact Or.inl ⟨h.1, ht⟩
    · exact Or.inr ⟨le_of_not_ge ht, h.2⟩

theorem half_images_inter :
    (P.map '' (Disk ×ˢ halfInterval false)) ∩
      (P.map '' (Disk ×ˢ halfInterval true)) = j '' Disk := by
  rw [← P.injective.image_inter (half_source_subset false) (half_source_subset true)]
  have hsource : (Disk ×ˢ halfInterval false) ∩ (Disk ×ˢ halfInterval true) =
      Disk ×ˢ {(0 : ℝ)} := by
    ext z
    simp only [halfInterval, Bool.false_eq_true, ↓reduceIte, mem_inter_iff,
      mem_prod, mem_Icc, mem_singleton_iff]
    constructor
    · intro h
      exact ⟨h.1.1, le_antisymm h.1.2.2 h.2.2.1⟩
    · rintro ⟨h, hz⟩
      rw [hz]
      norm_num [h]
  rw [hsource]
  ext x
  constructor
  · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨z,hz,(P.central z hz).symm⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨(z,0),⟨hz,rfl⟩,P.central z hz⟩

theorem cap_subset_half_boundary (b : Bool) : P.capDisk b ⊆ P.map '' halfBoundary b := by
  apply image_mono
  intro z hz
  apply Or.inr
  refine ⟨hz.1, ?_⟩
  cases b
  · exact Or.inl hz.2
  · exact Or.inr hz.2

theorem half_boundary_outside_cap (b : Bool) :
    ((P.map '' halfBoundary b) \ P.capDisk b).Nonempty := by
  have hz : (0 : V2) ∈ Disk := by simp
  have h0 : ((0 : V2), (0 : ℝ)) ∈ halfBoundary b := by
    apply Or.inr
    refine ⟨hz, ?_⟩
    cases b <;> simp
  refine ⟨P.map (0,0), ⟨(0,0),h0,rfl⟩, ?_⟩
  rintro ⟨z,hzcap,heq⟩
  have hh := P.injective (cap_source_subset b hzcap)
    (half_source_subset b (half_source_boundary_subset b h0)) heq
  have ht := congrArg Prod.snd hh
  have hzval : z.2 = (if b then (1 / 2 : ℝ) else -(1 / 2)) := hzcap.2
  cases b <;> norm_num at hzval <;> linarith

theorem cap_disjoint_opposite_half (b : Bool) :
    Disjoint (P.capDisk b) (P.map '' (Disk ×ˢ halfInterval (!b))) := by
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ ⟨w,hw,heq⟩
  have hh := P.injective (half_source_subset (!b) hw) (cap_source_subset b hz) heq
  have ht := congrArg Prod.snd hh
  have hzval : z.2 = (if b then (1 / 2 : ℝ) else -(1 / 2)) := hz.2
  have hwval := hw.2
  cases b <;> simp only [Bool.not_false, Bool.not_true, halfInterval,
    Bool.false_eq_true, ↓reduceIte, mem_Icc] at hzval hwval <;>
    linarith [hwval.1,hwval.2]

theorem cap_inter_frontier (b : Bool) :
    P.capDisk b ∩ frontier R = P.capRimSet b := by
  apply Subset.antisymm
  · rintro _ ⟨⟨z,hz,rfl⟩,hx⟩
    exact ⟨z,⟨(P.proper z (cap_source_subset b hz)).mp hx,hz.2⟩,rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    have hzd : z ∈ Disk ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)} :=
      ⟨sphere_subset_closedBall hz.1,hz.2⟩
    exact ⟨⟨z,hzd,rfl⟩,(P.proper z (cap_source_subset b hzd)).mpr hz.1⟩

theorem half_boundary_image_eq (b : Bool) :
    P.map '' halfBoundary b =
      ((P.map '' (Disk ×ˢ halfInterval b)) ∩ frontier R) ∪ P.capDisk b ∪ j '' Disk := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    rcases hz with hz | hz
    · have hzd : z ∈ Disk ×ˢ halfInterval b := ⟨sphere_subset_closedBall hz.1,hz.2⟩
      exact Or.inl (Or.inl ⟨⟨z,hzd,rfl⟩,
        (P.proper z (half_source_subset b hzd)).mpr hz.1⟩)
    · have he : z.2 = 0 ∨ z.2 = (if b then (1 / 2 : ℝ) else -(1 / 2)) := by
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, mem_prod, mem_insert_iff,
          mem_singleton_iff] at hz ⊢ <;> tauto
      rcases he with he | he
      · apply Or.inr
        refine ⟨z.1,hz.1,?_⟩
        simpa only [←he] using (P.central z.1 hz.1).symm
      · exact Or.inl (Or.inr ⟨z,⟨hz.1,he⟩,rfl⟩)
  · rintro x ((hx | hx) | hx)
    · obtain ⟨⟨z,hz,rfl⟩,hf⟩ := hx
      exact ⟨z,Or.inl ⟨(P.proper z (half_source_subset b hz)).mp hf,hz.2⟩,rfl⟩
    · exact P.cap_subset_half_boundary b hx
    · obtain ⟨z,hz,rfl⟩ := hx
      refine ⟨(z,0),Or.inr ⟨hz,?_⟩,P.central z hz⟩
      cases b <;> simp

end PoincareConjecture.M76.OriginalDiskProduct
