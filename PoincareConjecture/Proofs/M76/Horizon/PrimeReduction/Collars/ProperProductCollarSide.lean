import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.ProperDiskCollarSide

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem exists_proper_product_opposite_collar_half
    {X A T : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace T] [CompactSpace T] [PreconnectedSpace T]
    {K S O : Set X} (C : (A × I) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hSO : S ⊆ O)
    (hzero : ∀ z, (C z : X) ∈ S ↔ (z.2 : ℝ) = 0)
    (j : P2 × T → X) (hj : Continuous (fun z : Disk × T => j (z.1,z.2)))
    (hproper : ∀ z ∈ Disk, ∀ t : T, j (z,t) ∈ S ↔ z ∈ Rim) :
    ∃ (a δ : ℝ) (positive : Bool),
      0 < a ∧ a < 1 ∧ 0 < δ ∧ δ ≤ 1/2 ∧
      (∀ z : P2, ‖z‖ ∈ Icc a 1 → ∀ t : T, j (z,t) ∈ O) ∧
      (∀ z : P2, ‖z‖ ∈ Ico a 1 → ∀ t : T, ∀ w : A × I,
        (C w : X) = j (z,t) →
        if positive then 0 < (w.2 : ℝ) else (w.2 : ℝ) < 0) ∧
      ∀ w : A × I,
        (if positive then (w.2 : ℝ) ∈ Ico (-δ) 0 else (w.2 : ℝ) ∈ Ioc 0 δ) →
        (C w : X) ∉ j '' (Disk ×ˢ (univ : Set T)) := by
  classical
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let bad : Set (Disk × T) := (fun z : Disk × T => j (z.1,z.2)) ⁻¹' Oᶜ
  have hbad : IsCompact bad := (hO.isClosed_compl.preimage hj).isCompact
  have hlt (z : Disk × T) (hz : z ∈ bad) : ‖(z.1 : P2)‖ < 1 := by
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.1.property)
    intro heq
    exact hz (hSO ((hproper z.1 z.1.property z.2).mpr (mem_sphere_zero_iff_norm.mpr heq)))
  have hex : ∃ r : ℝ, r < 1 ∧ ∀ z ∈ bad, ‖(z.1 : P2)‖ ≤ r :=
    hbad.exists_forall_le' (α := OrderDual ℝ)
      (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).continuousOn hlt
  obtain ⟨r,hr,hrbad⟩ := hex
  obtain ⟨a,hra,ha1⟩ := exists_between (max_lt hr zero_lt_one)
  have ha : 0 < a := (le_max_right r 0).trans_lt hra
  have hmaps (z : P2) (hz : ‖z‖ ∈ Icc a 1) (t : T) : j (z,t) ∈ O := by
    by_contra hn
    have hh := hrbad (⟨z,mem_closedBall_zero_iff.mpr hz.2⟩,t) hn
    exact (not_lt_of_ge (hz.1.trans hh)) ((le_max_left r 0).trans_lt hra)
  let shell := {z : P2 | ‖z‖ ∈ Ico a 1}
  have hshell := isConnected_half_open_square_shell ha ha1
  let : PreconnectedSpace shell := isPreconnected_iff_preconnectedSpace.mp hshell.isPreconnected
  let lift : shell × T → K := fun z =>
    ⟨j (z.1,z.2),hOK (hmaps z.1 ⟨z.1.property.1,z.1.property.2.le⟩ z.2)⟩
  have hlift : Continuous lift := by
    apply Continuous.subtype_mk
    exact hj.comp (((continuous_subtype_val.comp continuous_fst).subtype_mk
      (fun z => mem_closedBall_zero_iff.mpr z.1.property.2.le)).prodMk continuous_snd)
  let height : shell × T → ℝ := fun z => (C.symm (lift z)).2
  have hheight : Continuous height :=
    continuous_subtype_val.comp (continuous_snd.comp (C.symm.continuous.comp hlift))
  have hnonzero (z : shell × T) : height z ≠ 0 := by
    intro hz
    have hm := (hzero (C.symm (lift z))).mpr hz
    rw [C.apply_symm_apply] at hm
    have hrim := (hproper z.1 (mem_closedBall_zero_iff.mpr z.1.property.2.le) z.2).mp hm
    exact (ne_of_lt z.1.property.2) (mem_sphere_zero_iff_norm.mp hrim)
  have hsign := isPreconnected_univ.mapsTo_Ioi_or_Iio hheight.continuousOn
    (fun z _ => hnonzero z)
  obtain ⟨positive,hsign⟩ : ∃ positive : Bool, ∀ z : shell × T,
      if positive then 0 < height z else height z < 0 := by
    rcases hsign with hpos | hneg
    · exact ⟨true,fun z => hpos (mem_univ z)⟩
    · exact ⟨false,fun z => hneg (mem_univ z)⟩
  have hwholeSign (z : P2) (hz : ‖z‖ ∈ Ico a 1) (t : T) (w : A × I)
      (hw : (C w : X) = j (z,t)) :
      if positive then 0 < (w.2 : ℝ) else (w.2 : ℝ) < 0 := by
    have heq : C w = lift (⟨z,hz⟩,t) := Subtype.ext hw
    have hh : C.symm (lift (⟨z,hz⟩,t)) = w := by rw [←heq,C.symm_apply_apply]
    simpa only [height,hh] using hsign (⟨z,hz⟩,t)
  let core := j '' (closedBall (0 : P2) a ×ˢ (univ : Set T))
  have hcore : IsCompact core := by
    let d : Set (Disk × T) := {z | ‖(z.1 : P2)‖ ≤ a}
    have hd : IsCompact d := (isClosed_le
      (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)) continuous_const).isCompact
    have heq : core = (fun z : Disk × T => j (z.1,z.2)) '' d := by
      apply Subset.antisymm
      · rintro _ ⟨⟨z,t⟩,⟨hz,_⟩,rfl⟩
        exact ⟨(⟨z,closedBall_subset_closedBall ha1.le hz⟩,t),mem_closedBall_zero_iff.mp hz,rfl⟩
      · rintro _ ⟨⟨z,t⟩,hz,rfl⟩
        exact ⟨(z,t),⟨mem_closedBall_zero_iff.mpr hz,mem_univ t⟩,rfl⟩
    rw [heq]
    exact hd.image hj
  have hzeroCore (x : A) : (C (x,⟨0,by norm_num⟩) : X) ∈ coreᶜ := by
    rintro ⟨⟨z,t⟩,⟨hz,_⟩,heq⟩
    have hzD := closedBall_subset_closedBall ha1.le hz
    have hzS : j (z,t) ∈ S := heq ▸ (hzero (x,⟨0,by norm_num⟩)).mpr rfl
    have hz1 := mem_sphere_zero_iff_norm.mp ((hproper z hzD t).mp hzS)
    have hza := mem_closedBall_zero_iff.mp hz
    linarith
  obtain ⟨δ,hδ,hδhalf,hthin⟩ :=
    (continuous_subtype_val.comp C.continuous).exists_closed_strip_subset
      hcore.isClosed.isOpen_compl hzeroCore
  refine ⟨a,δ,positive,ha,ha1,hδ,hδhalf,hmaps,hwholeSign,?_⟩
  intro w hw hwdisk
  obtain ⟨⟨z,t⟩,⟨hz,_⟩,heq⟩ := hwdisk
  have htime : |(w.2 : ℝ)| ≤ δ := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw ⊢ <;>
      exact abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have hnotcore := hthin w.1 w.2 htime
  have haz : a < ‖z‖ := by
    by_contra hn
    exact hnotcore ⟨(z,t),⟨mem_closedBall_zero_iff.mpr (le_of_not_gt hn),mem_univ t⟩,heq⟩
  have htime0 : (w.2 : ℝ) ≠ 0 := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw ⊢ <;> linarith [hw.1,hw.2]
  have hzlt : ‖z‖ < 1 := by
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hz)
    intro hz1
    have hzS := (hproper z hz t).mpr (mem_sphere_zero_iff_norm.mpr hz1)
    exact htime0 ((hzero w).mp (heq ▸ hzS))
  have hs := hwholeSign z ⟨haz.le,hzlt⟩ t w heq.symm
  cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw hs <;> linarith [hw.1,hw.2]

end PoincareConjecture.M76
