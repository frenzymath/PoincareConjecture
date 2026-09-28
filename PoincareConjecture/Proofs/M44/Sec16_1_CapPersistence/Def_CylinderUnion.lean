import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderUniqueness










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M44





theorem exists_cylinder_of_coverage
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale B : ℝ} {U : Set C.carrier} {ι : Type v}
    (b : ι → ℝ) (e : ∀ i, SurgeryFlowCylinder F C origin scale (Ico 0 (b i)) U)
    (hB : 0 < B) (hcover : ∀ s ∈ Ico 0 B, ∃ i, s < b i)
    (hinit : ∀ i j (hi : 0 < b i) (hj : 0 < b j), ∀ x ∈ U,
      (e i).forward 0 ⟨le_rfl, hi⟩ x = (e j).forward 0 ⟨le_rfl, hj⟩ x) :
    ∃ E : SurgeryFlowCylinder F C origin scale (Ico 0 B) U,
      ∀ i s (hs : s ∈ Ico 0 (b i)) (hs' : s ∈ Ico 0 B), ∀ x ∈ U,
        E.forward s hs' x = (e i).forward s hs x := by
  classical
  let pick (s : ℝ) (hs : s ∈ Ico 0 B) : ι := Classical.choose (hcover s hs)
  have hpick (s : ℝ) (hs : s ∈ Ico 0 B) : s ∈ Ico 0 (b (pick s hs)) :=
    ⟨hs.1, Classical.choose_spec (hcover s hs)⟩
  let forward (s : ℝ) (hs : s ∈ Ico 0 B) := (e (pick s hs)).forward s (hpick s hs)
  let inverse (s : ℝ) (hs : s ∈ Ico 0 B) := (e (pick s hs)).inverse s (hpick s hs)
  have hmatch (s : ℝ) (hs : s ∈ Ico 0 B) (i : ι) (hi : s < b i)
      (x : C.carrier) (hx : x ∈ U) :
      forward s hs x = (e i).forward s ⟨hs.1, hi⟩ x := by
    apply cylinder_forward_eq_of_initial (e (pick s hs)) (e i) hs.1
      (fun _ ht => ⟨ht.1, ht.2.trans_lt (hpick s hs).2⟩)
      (fun _ ht => ⟨ht.1, ht.2.trans_lt hi⟩) x hx hx
    exact hinit (pick s hs) i (hs.1.trans_lt (hpick s hs).2) (hs.1.trans_lt hi) x hx
  have hscale := (e (pick 0 ⟨le_rfl, hB⟩)).scale_pos
  have hclock : StrictMono (fun s : ℝ => origin + s / scale) := by
    intro s t hst
    dsimp only
    linarith [(div_lt_div_iff_of_pos_right hscale).mpr hst]
  let E : SurgeryFlowCylinder F C origin scale (Ico 0 B) U := {
    scale_pos := hscale
    interval_connected := ordConnected_Ico
    time_subset := by
      rintro _ ⟨s, hs, rfl⟩
      exact (e (pick s hs)).time_subset (mem_image_of_mem _ (hpick s hs))
    forward := forward
    inverse := inverse
    forward_smooth := fun s hs => (e (pick s hs)).forward_smooth s (hpick s hs)
    inverse_smooth := fun s hs => (e (pick s hs)).inverse_smooth s (hpick s hs)
    left_inverse := fun s hs => (e (pick s hs)).left_inverse s (hpick s hs)
    right_inverse := fun s hs => (e (pick s hs)).right_inverse s (hpick s hs)
    slab_compatibility := by
      intro a d had hJ hNo s hs t ht hs' ht' x hx
      obtain ⟨i, hi⟩ := hcover (max s t) ⟨le_max_of_le_left hs.1, max_lt hs.2 ht.2⟩
      have hsi : s < b i := (le_max_left _ _).trans_lt hi
      have hti : t < b i := (le_max_right _ _).trans_lt hi
      rw [hmatch s hs i hsi x hx, hmatch t ht i hti x hx]
      exact (e i).slab_compatibility a d had hJ hNo
        s ⟨hs.1, hsi⟩ t ⟨ht.1, hti⟩ hs' ht' x hx
    retained_at_surgery := by
      intro s hs hT _ hearlier
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := hcover s hs
      rw [hmatch s hs i hi x hx]
      obtain ⟨t, ht, hts⟩ := hearlier
      exact (e i).retained_at_surgery s ⟨hs.1, hi⟩ hT
        ⟨t, ⟨ht.1, hts.trans hi⟩, hts⟩ (mem_image_of_mem _ hx)
    pre_retained_at_surgery := by
      intro s hs hT _ t ht ht' x hx
      obtain ⟨i, hi⟩ := hcover s hs
      have hti : t < b i := (hclock.lt_iff_lt.mp ht'.2).trans hi
      rw [hmatch t ht i hti x hx]
      exact (e i).pre_retained_at_surgery s ⟨hs.1, hi⟩ hT t ⟨ht.1, hti⟩ ht' x hx
    surgery_compatibility := by
      intro s hs hT _ t ht ht' x hx
      obtain ⟨i, hi⟩ := hcover s hs
      have hti : t < b i := (hclock.lt_iff_lt.mp ht'.2).trans hi
      rw [hmatch t ht i hti x hx, hmatch s hs i hi x hx]
      exact (e i).surgery_compatibility s ⟨hs.1, hi⟩ hT t ⟨ht.1, hti⟩ ht' x hx
  }
  exact ⟨E, fun i s hs hs' x hx => hmatch s hs' i hs.2 x hx⟩

end PoincareConjecture.M44
