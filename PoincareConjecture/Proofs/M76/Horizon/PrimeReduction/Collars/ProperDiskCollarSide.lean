import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusSides
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem exists_proper_disk_opposite_collar_half
    {X A : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [CompactSpace A]
    {K S O : Set X} (C : (A × I) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K) (hSO : S ⊆ O)
    (hzero : ∀ z, (C z : X) ∈ S ↔ (z.2 : ℝ) = 0)
    (j : P2 → X) (hj : ContinuousOn j Disk)
    (hproper : ∀ z ∈ Disk, j z ∈ S ↔ z ∈ Rim) :
    ∃ (a δ : ℝ) (positive : Bool),
      0 < a ∧ a < 1 ∧ 0 < δ ∧ δ ≤ 1 / 2 ∧
      MapsTo j {z : P2 | ‖z‖ ∈ Icc a 1} O ∧
      (∀ z : P2, ‖z‖ ∈ Ico a 1 → ∀ w : A × I, (C w : X) = j z →
        if positive then 0 < (w.2 : ℝ) else (w.2 : ℝ) < 0) ∧
      ∀ w : A × I,
        (if positive then (w.2 : ℝ) ∈ Ico (-δ) 0 else (w.2 : ℝ) ∈ Ioc 0 δ) →
        (C w : X) ∉ j '' Disk := by
  classical
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let bad : Set Disk := (fun z : Disk => j z) ⁻¹' Oᶜ
  have hbad : IsCompact bad := (hO.isClosed_compl.preimage hj.domRestrict).isCompact
  have hlt (z : Disk) (hz : z ∈ bad) : ‖(z : P2)‖ < 1 := by
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
    intro heq
    exact hz (hSO ((hproper z z.property).mpr (mem_sphere_zero_iff_norm.mpr heq)))
  have hex : ∃ r : ℝ, r < 1 ∧ ∀ z ∈ bad, ‖(z : P2)‖ ≤ r :=
    hbad.exists_forall_le' (α := OrderDual ℝ)
      (continuous_norm.comp continuous_subtype_val).continuousOn hlt
  obtain ⟨r, hr, hrbad⟩ := hex
  obtain ⟨a, hra, ha1⟩ := exists_between (max_lt hr zero_lt_one)
  have ha : 0 < a := (le_max_right r 0).trans_lt hra
  have hmaps : MapsTo j {z : P2 | ‖z‖ ∈ Icc a 1} O := by
    intro z hz
    by_contra hnot
    have hbound := hrbad ⟨z,mem_closedBall_zero_iff.mpr hz.2⟩ hnot
    have hral : r < a := (le_max_left r 0).trans_lt hra
    exact (not_lt_of_ge (hz.1.trans hbound)) hral
  let shell := {z : P2 | ‖z‖ ∈ Ico a 1}
  have hshell := isConnected_half_open_square_shell ha ha1
  let : PreconnectedSpace shell := isPreconnected_iff_preconnectedSpace.mp hshell.isPreconnected
  let lift : shell → K := fun z =>
    ⟨j z,hOK (hmaps ⟨z.property.1,z.property.2.le⟩)⟩
  have hlift : Continuous lift := by
    apply Continuous.subtype_mk
    exact hj.comp_continuous continuous_subtype_val
      (fun z => mem_closedBall_zero_iff.mpr z.property.2.le)
  let height : shell → ℝ := fun z => (C.symm (lift z)).2
  have hheight : Continuous height :=
    continuous_subtype_val.comp (continuous_snd.comp (C.symm.continuous.comp hlift))
  have hnonzero (z : shell) : height z ≠ 0 := by
    intro hz
    have hm := (hzero (C.symm (lift z))).mpr hz
    rw [C.apply_symm_apply] at hm
    have hrim := (hproper z (mem_closedBall_zero_iff.mpr z.property.2.le)).mp hm
    exact (ne_of_lt z.property.2) (mem_sphere_zero_iff_norm.mp hrim)
  have hsign := isPreconnected_univ.mapsTo_Ioi_or_Iio hheight.continuousOn
    (fun z _ => hnonzero z)
  obtain ⟨positive, hsign⟩ : ∃ positive : Bool, ∀ z : shell,
      if positive then 0 < height z else height z < 0 := by
    rcases hsign with hpos | hneg
    · exact ⟨true,fun z => hpos (mem_univ z)⟩
    · exact ⟨false,fun z => hneg (mem_univ z)⟩
  have hwholeSign (z : P2) (hz : ‖z‖ ∈ Ico a 1) (w : A × I)
      (hw : (C w : X) = j z) :
      if positive then 0 < (w.2 : ℝ) else (w.2 : ℝ) < 0 := by
    have heq : C w = lift ⟨z,hz⟩ := Subtype.ext hw
    have hh : C.symm (lift ⟨z,hz⟩) = w := by rw [←heq,C.symm_apply_apply]
    simpa only [height,hh] using hsign ⟨z,hz⟩
  let core := j '' closedBall (0 : P2) a
  have hcore : IsCompact core := (isCompact_closedBall _ _).image_of_continuousOn
    (hj.mono (closedBall_subset_closedBall ha1.le))
  have hzeroCore (x : A) : (C (x,⟨0,by norm_num⟩) : X) ∈ coreᶜ := by
    rintro ⟨z,hz,heq⟩
    have hzD := closedBall_subset_closedBall ha1.le hz
    have hzS : j z ∈ S := heq ▸ (hzero (x,⟨0,by norm_num⟩)).mpr rfl
    have hz1 := mem_sphere_zero_iff_norm.mp ((hproper z hzD).mp hzS)
    have hza := mem_closedBall_zero_iff.mp hz
    linarith
  obtain ⟨δ,hδ,hδhalf,hthin⟩ :=
    (continuous_subtype_val.comp C.continuous).exists_closed_strip_subset
      hcore.isClosed.isOpen_compl hzeroCore
  refine ⟨a,δ,positive,ha,ha1,hδ,hδhalf,hmaps,hwholeSign,?_⟩
  intro w hw hwdisk
  obtain ⟨z,hz,heq⟩ := hwdisk
  have htime : |(w.2 : ℝ)| ≤ δ := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw ⊢ <;>
      exact abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have hnotcore := hthin w.1 w.2 htime
  have haz : a < ‖z‖ := by
    by_contra h
    exact hnotcore ⟨z,mem_closedBall_zero_iff.mpr (le_of_not_gt h),heq⟩
  have htime0 : (w.2 : ℝ) ≠ 0 := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw ⊢ <;> linarith [hw.1,hw.2]
  have hzlt : ‖z‖ < 1 := by
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hz)
    intro hz1
    have hzS := (hproper z hz).mpr (mem_sphere_zero_iff_norm.mpr hz1)
    exact htime0 ((hzero w).mp (heq ▸ hzS))
  have hs := hwholeSign z ⟨haz.le,hzlt⟩ w heq.symm
  cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw hs <;> linarith [hw.1,hw.2]

end PoincareConjecture.M76
