import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripCenterCuts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

def halfSource (positive : Bool) : Set P2 :=
  Icc (0 : ℝ) 1 ×ˢ if positive then Icc (0 : ℝ) 1 else Icc (-1 : ℝ) 0

def farArmParameter (positive : Bool) : ℝ := if positive then 1 else -1

theorem halfSource_subset_source (positive : Bool) : halfSource positive ⊆ source := by
  cases positive with
  | false => exact fun x hx => ⟨hx.1, hx.2.1, hx.2.2.trans (by norm_num)⟩
  | true => exact fun x hx => ⟨hx.1, le_trans (by norm_num) hx.2.1, hx.2.2⟩

theorem arm_zero_subset_halfSource (positive : Bool) : arm 0 ⊆ halfSource positive := by
  intro x hx
  have hx0 : x.2 = 0 := hx.2
  cases positive <;> exact ⟨hx.1, by rw [hx0]; norm_num⟩

theorem farArmParameter_ne_zero (positive : Bool) : farArmParameter positive ≠ 0 := by
  cases positive <;> norm_num [farArmParameter]

theorem halfSource_union (positive : Bool) :
    halfSource positive ∪ halfSource (!positive) = source := by
  have hinterval : Icc (-1 : ℝ) 0 ∪ Icc (0 : ℝ) 1 = Icc (-1 : ℝ) 1 :=
    Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
  cases positive with
  | false =>
      change (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ∪
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = _
      rw [← prod_union, hinterval]
      rfl
  | true =>
      change (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∪
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) = _
      rw [union_comm, ← prod_union, hinterval]
      rfl

theorem arm_far_subset_source (positive : Bool) :
    arm (farArmParameter positive) ⊆ source := by
  intro x hx
  have hxfar : x.2 = farArmParameter positive := hx.2
  refine ⟨hx.1, ?_⟩
  rw [hxfar]
  cases positive <;> norm_num [farArmParameter]

theorem disjoint_center_far_images
    {E : Type*} (c : P2 → E) (hci : InjOn c source) (positive : Bool) :
    Disjoint (c '' arm 0) (c '' arm (farArmParameter positive)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxS := halfSource_subset_source false (arm_zero_subset_halfSource false hx)
  have heq := hci (arm_far_subset_source positive hy) hxS hyx
  have hyfar : y.2 = farArmParameter positive := hy.2
  have hx0 : x.2 = 0 := hx.2
  exact farArmParameter_ne_zero positive
    (hyfar.symm.trans ((congrArg Prod.snd heq).trans hx0))

private theorem exists_half_strip_attaching_arc_of_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (lo hi far : ℝ) (hlohi : lo < hi) (hlo : -1 ≤ lo) (hhi : hi ≤ 1)
    (hpair : ({lo, hi} : Set ℝ) = {0, far}) (hfar0 : far ≠ 0)
    {A QA Q : Set E} (c : P2 → E)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hhalfA : c '' (Icc (0 : ℝ) 1 ×ˢ Icc lo hi) ⊆ A)
    (hQA : QA = (A ∩ Q) ∪ c '' arm 0) :
    let H := c '' (Icc (0 : ℝ) 1 ×ˢ Icc lo hi)
    let W := c '' arm far
    ∃ U : Set E,
      IsFinitePLBallPair P2 H (U ∪ W) ∧
      IsFinitePLBallPair ℝ U {c (0, far), c (1, far)} ∧ U ⊆ QA ∧
      IsFinitePLBallPair ℝ W {c (0, far), c (1, far)} ∧ c (0, far) ≠ c (1, far) ∧
      W \ {c (0, far), c (1, far)} ⊆ A \ QA := by
  let D := Icc (0 : ℝ) 1 ×ˢ Icc lo hi
  let R := ({0, 1} : Set ℝ) ×ˢ Icc lo hi ∪
    Icc (0 : ℝ) 1 ×ˢ {lo, hi}
  have hD : IsFinitePLBallPair P2 D R :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc hlohi)
  have hDS : D ⊆ source := fun x hx => ⟨hx.1, hlo.trans hx.2.1, hx.2.2.trans hhi⟩
  have hfar : IsFinitePLBallPair ℝ (arm far) {(0, far), (1, far)} :=
    (exists_arm_parameter far).1
  have hfarR : arm far ⊆ R := by
    intro x hx
    refine Or.inr ⟨hx.1, ?_⟩
    rw [hpair]
    exact Or.inr hx.2
  have hfarD := hfarR.trans hD.1
  have hends : ((0, far) : P2) ≠ (1, far) := by
    intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst h
    norm_num at h01
  obtain ⟨U, hU, hfarU, hfarUi⟩ := hD.exists_boundary_arc_complement hfar hfarR hends
  have hUD : U ⊆ D := (subset_union_right.trans hfarU.subset).trans hD.1
  have hhalf : IsFinitePLBallPair P2 (c '' D) (c '' U ∪ c '' arm far) := by
    have h := hD.image_of_subset hcPL hDS hci
    rw [← hfarU, image_union, union_comm] at h
    exact h
  have hUimage : IsFinitePLBallPair ℝ (c '' U) {c (0, far), c (1, far)} := by
    simpa only [image_pair] using hU.image_of_subset hcPL (hUD.trans hDS) hci
  have hWimage : IsFinitePLBallPair ℝ (c '' arm far) {c (0, far), c (1, far)} := by
    simpa only [image_pair] using hfar.image_of_subset hcPL (hfarD.trans hDS) hci
  have hUQA : c '' U ⊆ QA := by
    rintro y ⟨x, hxU, rfl⟩
    rw [hQA]
    have hxD := hUD hxU
    have hxR : x ∈ R := hfarU.subset (Or.inr hxU)
    have hendsQ (ht : x.1 = 0 ∨ x.1 = 1) : c x ∈ (A ∩ Q) ∪ c '' arm 0 :=
      Or.inl ⟨hhalfA ⟨x, hxD, rfl⟩, (hcQ x (hDS hxD)).mpr ht⟩
    rcases hxR with ⟨ht, _⟩ | ⟨ht, hu⟩
    · exact hendsQ ht
    · rw [hpair] at hu
      rcases hu with hzero | hfarval
      · exact Or.inr ⟨x, ⟨ht, hzero⟩, rfl⟩
      · have hxends := hfarUi.subset ⟨⟨ht, hfarval⟩, hxU⟩
        rcases hxends with hx | hx
        · exact hendsQ (Or.inl (congrArg Prod.fst hx))
        · exact hendsQ (Or.inr (congrArg Prod.fst hx))
  have hendsImage : c (0, far) ≠ c (1, far) := by
    intro h
    exact hends (hci (hDS (hfarD (hfar.1 (by simp))))
      (hDS (hfarD (hfar.1 (by simp)))) h)
  have hproper : (c '' arm far) \ {c (0, far), c (1, far)} ⊆ A \ QA := by
    rintro y ⟨⟨x, hx, rfl⟩, hnot⟩
    have hxD := hfarD hx
    refine ⟨hhalfA ⟨x, hxD, rfl⟩, ?_⟩
    rw [hQA]
    rintro (⟨_, hxQ⟩ | ⟨z, hz, hzx⟩)
    · rcases (hcQ x (hDS hxD)).mp hxQ with ht | ht
      · have heq : x = (0, far) := Prod.ext ht hx.2
        exact hnot (by simp only [heq, mem_insert_iff, mem_singleton_iff, true_or])
      · have heq : x = (1, far) := Prod.ext ht hx.2
        exact hnot (by simp only [heq, mem_insert_iff, mem_singleton_iff, or_true])
    · have hz0 : z.2 = 0 := hz.2
      have hzS : z ∈ source := ⟨hz.1, by rw [hz0]; norm_num⟩
      have hzx' := hci hzS (hDS hxD) hzx
      have hxzero : x.2 = 0 := hzx' ▸ hz.2
      exact hfar0 (hx.2.symm.trans hxzero)
  exact ⟨c '' U, hhalf, hUimage, hUQA, hWimage, hendsImage, hproper⟩

theorem exists_half_strip_attaching_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A QA Q : Set E} (c : P2 → E) (positive : Bool)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hhalfA : c '' halfSource positive ⊆ A)
    (hQA : QA = (A ∩ Q) ∪ c '' arm 0) :
    let H := c '' halfSource positive
    let W := c '' arm (farArmParameter positive)
    ∃ U : Set E,
      IsFinitePLBallPair P2 H (U ∪ W) ∧
      IsFinitePLBallPair ℝ U {c (0, farArmParameter positive), c (1, farArmParameter positive)} ∧
      U ⊆ QA ∧
      IsFinitePLBallPair ℝ W {c (0, farArmParameter positive), c (1, farArmParameter positive)} ∧
      c (0, farArmParameter positive) ≠ c (1, farArmParameter positive) ∧
      W \ {c (0, farArmParameter positive), c (1, farArmParameter positive)} ⊆ A \ QA := by
  cases positive with
  | false =>
      exact exists_half_strip_attaching_arc_of_bounds (-1) 0 (-1) (by norm_num)
        le_rfl (by norm_num) (by rw [pair_comm]) (by norm_num)
        c hcPL hci hcQ hhalfA hQA
  | true =>
      exact exists_half_strip_attaching_arc_of_bounds 0 1 1 (by norm_num)
        (by norm_num) le_rfl rfl one_ne_zero c hcPL hci hcQ hhalfA hQA

theorem exists_lower_half_strip_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A QA Q : Set E} (hA : IsFinitePLBallPair P2 A QA) (c : P2 → E)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hhalfA : c '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ⊆ A)
    (hQA : QA = (A ∩ Q) ∪ c '' arm 0) :
    let H := c '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0)
    let W := c '' arm (-1)
    ∃ V : Set E,
      IsFinitePLBallPair ℝ V {c (0, -1), c (1, -1)} ∧
      IsFinitePLBallPair P2 (A \ (H \ W)) (W ∪ V) ∧
      H ∪ (A \ (H \ W)) = A ∧ H ∩ (A \ (H \ W)) = W ∧
      (A \ (H \ W)) ∩ QA = V := by
  obtain ⟨U, hH, hU, hUQA, hW, hends, hproper⟩ :=
    exists_half_strip_attaching_arc c false hcPL hci hcQ hhalfA hQA
  obtain ⟨V, hV, _, _, hcomp, hcover, hinter, _, hcontact⟩ :=
    hA.exists_boundary_attached_disk_complement hH hhalfA hU hUQA hW hends hproper
  exact ⟨V, hV, hcomp, hcover, hinter, hcontact⟩

theorem exists_upper_half_strip_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A QA Q : Set E} (hA : IsFinitePLBallPair P2 A QA) (c : P2 → E)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hhalfA : c '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hQA : QA = (A ∩ Q) ∪ c '' arm 0) :
    let H := c '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    let W := c '' arm 1
    ∃ V : Set E,
      IsFinitePLBallPair ℝ V {c (0, 1), c (1, 1)} ∧
      IsFinitePLBallPair P2 (A \ (H \ W)) (W ∪ V) ∧
      H ∪ (A \ (H \ W)) = A ∧ H ∩ (A \ (H \ W)) = W ∧
      (A \ (H \ W)) ∩ QA = V := by
  obtain ⟨U, hH, hU, hUQA, hW, hends, hproper⟩ :=
    exists_half_strip_attaching_arc c true hcPL hci hcQ hhalfA hQA
  obtain ⟨V, hV, _, _, hcomp, hcover, hinter, _, hcontact⟩ :=
    hA.exists_boundary_attached_disk_complement hH hhalfA hU hUQA hW hends hproper
  exact ⟨V, hV, hcomp, hcover, hinter, hcontact⟩

theorem half_strip_disk_complement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A QA Q : Set E} (hA : IsFinitePLBallPair P2 A QA) (c : P2 → E) (positive : Bool)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hhalfA : c '' halfSource positive ⊆ A)
    (hQA : QA = (A ∩ Q) ∪ c '' arm 0) :
    let H := c '' halfSource positive
    let W := c '' arm (farArmParameter positive)
    let C := A \ (H \ W)
    IsFinitePLBallPair P2 C ((C ∩ Q) ∪ W) ∧ H ∪ C = A ∧ H ∩ C = W ∧
      Disjoint C (c '' arm 0) ∧
      IsFinitePLBallPair ℝ W {c (0, farArmParameter positive), c (1, farArmParameter positive)} := by
  let H := c '' halfSource positive
  let W := c '' arm (farArmParameter positive)
  let C := A \ (H \ W)
  obtain ⟨U, hH, hU, hUQA, hW, hends, hproper⟩ :=
    exists_half_strip_attaching_arc c positive hcPL hci hcQ hhalfA hQA
  obtain ⟨V, _, _, _, hcomp, hcover, hinter, _, hcontact⟩ :=
    hA.exists_boundary_attached_disk_complement hH hhalfA hU hUQA hW hends hproper
  have hnoCenter : Disjoint C (c '' arm 0) := by
    apply Set.disjoint_left.mpr
    intro x hxC hxcenter
    apply hxC.2
    refine ⟨(image_mono (arm_zero_subset_halfSource positive)) hxcenter, ?_⟩
    exact fun hxW => Set.disjoint_left.mp (disjoint_center_far_images c hci positive) hxcenter hxW
  have hV : V = C ∩ Q := by
    rw [← hcontact, hQA]
    ext x
    constructor
    · rintro ⟨hxC, ⟨_, hxQ⟩ | hxcenter⟩
      · exact ⟨hxC, hxQ⟩
      · exact False.elim (Set.disjoint_left.mp hnoCenter hxC hxcenter)
    · rintro ⟨hxC, hxQ⟩
      exact ⟨hxC, Or.inl ⟨hxC.1, hxQ⟩⟩
  refine ⟨?_, hcover, hinter, hnoCenter, hW⟩
  simpa only [hV, union_comm] using hcomp

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
