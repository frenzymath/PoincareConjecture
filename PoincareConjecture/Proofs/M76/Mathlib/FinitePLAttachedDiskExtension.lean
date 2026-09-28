import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryAttachedDisk
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension











set_option autoImplicit false

open Set Geometry

namespace Set

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]






theorem IsFinitePLBallPair.exists_extension_of_attached_disk
    {s q d u w : Set X} {t r D U W : Set Y} {a b : X} {A B : Y}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (ht : IsFinitePLBallPair (ℝ × ℝ) t r)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (u ∪ w)) (hds : d ⊆ s)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (U ∪ W)) (hDt : D ⊆ t)
    (hu : IsFinitePLBallPair ℝ u {a, b}) (huq : u ⊆ q)
    (hw : IsFinitePLBallPair ℝ w {a, b}) (hab : a ≠ b)
    (hproper : w \ {a, b} ⊆ s \ q)
    (hU : IsFinitePLBallPair ℝ U {A, B}) (hUr : U ⊆ r)
    (hW : IsFinitePLBallPair ℝ W {A, B}) (hAB : A ≠ B)
    (hProper : W \ {A, B} ⊆ t \ r)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hmemu : ∀ x : d, (x : X) ∈ u ↔ (e x : Y) ∈ U)
    (hmemw : ∀ x : d, (x : X) ∈ w ↔ (e x : Y) ∈ W) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : d, H ⟨x, hds x.property⟩ = ⟨e x, hDt (e x).property⟩) ∧
      (∀ x : s, (x : X) ∈ d ↔ (H x : Y) ∈ D) ∧
      (∀ x : s, (x : X) ∈ s \ (d \ w) ↔ (H x : Y) ∈ t \ (D \ W)) ∧
      ∀ x : s, (x : X) ∈ q ↔ (H x : Y) ∈ r := by
  obtain ⟨v, hv, hq, huv, hc, hunion, hinter, houter, hcouter⟩ :=
    hs.exists_boundary_attached_disk_complement hd hds hu huq hw hab hproper
  obtain ⟨V, hV, hr, hUV, hC, hUnion, hInter, hOuter, hCouter⟩ :=
    ht.exists_boundary_attached_disk_complement hD hDt hU hUr hW hAB hProper
  let c := s \ (d \ w)
  let C := t \ (D \ W)
  have hvq : v ⊆ q := subset_union_right.trans hq.subset
  have hVr : V ⊆ r := subset_union_right.trans hr.subset
  have hcontact (z : Set X) (hz : {a, b} ⊆ z) (hzq : z ⊆ q) :
      z ∩ w = {a, b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxp
      exact (hproper ⟨hx.2, hxp⟩).2 (hzq hx.1)
    · intro x hx
      exact ⟨hz hx, hw.1 hx⟩
  have hContact (Z : Set Y) (hZ : {A, B} ⊆ Z) (hZr : Z ⊆ r) :
      Z ∩ W = {A, B} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxp
      exact (hProper ⟨hx.2, hxp⟩).2 (hZr hx.1)
    · intro x hx
      exact ⟨hZ hx, hW.1 hx⟩
  have huw := hcontact u hu.1 huq
  have hvw := hcontact v hv.1 hvq
  have hUW := hContact U hU.1 hUr
  have hVW := hContact V hV.1 hVr
  have hwd : w ⊆ d := subset_union_right.trans hd.1
  have hWD : W ⊆ D := subset_union_right.trans hD.1
  let ew := e.restrictSubsets hwd hWD hmemw
  have hwcopy := hw
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKw, _⟩, _⟩, _⟩ := hwcopy
  have hew : ew.IsFinitePL := he.restrictSubsets hwd hWD hmemw K hK hKw
  have hends (x : w) : (x : X) ∈ ({a, b} : Set X) ↔
      (ew x : Y) ∈ ({A, B} : Set Y) := by
    have hx : (x : X) ∈ ({a, b} : Set X) ↔ (x : X) ∈ u := by
      rw [← huw]
      simp only [mem_inter_iff, x.property, and_true]
    have hy : (ew x : Y) ∈ U ↔ (ew x : Y) ∈ ({A, B} : Set Y) := by
      rw [← hUW]
      simp only [mem_inter_iff, (ew x).property, and_true]
    exact hx.trans ((hmemu ⟨x, hwd x.property⟩).trans hy)
  have hcvw : IsFinitePLBallPair (ℝ × ℝ) c (v ∪ w) := by
    simpa only [union_comm] using hc
  have hCVW : IsFinitePLBallPair (ℝ × ℝ) C (V ∪ W) := by
    simpa only [union_comm] using hC
  obtain ⟨ec, hec, hecw, hecv, hecwmem⟩ :=
    hcvw.exists_extension_of_boundary_piece hCVW hv hV hvw hVW ew hew hends
  have hoverlap (x : d) : (x : X) ∈ c ↔ (e x : Y) ∈ C := by
    have hx : (x : X) ∈ c ↔ (x : X) ∈ w := by
      rw [← hinter]
      simp only [c, mem_inter_iff, x.property, true_and]
    have hy : (e x : Y) ∈ W ↔ (e x : Y) ∈ C := by
      rw [← hInter]
      simp only [C, mem_inter_iff, (e x).property, true_and]
    exact hx.trans ((hmemw x).trans hy)
  have hagree (x : X) (hxd : x ∈ d) (hxc : x ∈ c) :
      (e ⟨x, hxd⟩ : Y) = (ec ⟨x, hxc⟩ : Y) := by
    have hxw : x ∈ w := hinter ▸ And.intro hxd hxc
    exact (congrArg (fun y : C => (y : Y)) (hecw ⟨x, hxw⟩)).symm
  obtain ⟨H₀, hH₀, hH₀d, hH₀c⟩ :=
    Homeomorph.exists_union_finitePL e ec he hec hoverlap hagree
  let H : s ≃ₜ t := (Homeomorph.setCongr hunion.symm).trans
    (H₀.trans (Homeomorph.setCongr hUnion))
  have hH : H.IsFinitePL := by
    obtain ⟨f, hf, hHf⟩ := hH₀
    rw [hunion] at hf
    exact ⟨f, hf, fun x => hHf ⟨x, hunion.symm ▸ x.property⟩⟩
  have hkeep (x : d) : H ⟨x, hds x.property⟩ = ⟨e x, hDt (e x).property⟩ :=
    Subtype.ext (hH₀d x)
  have hcs : c ⊆ s := subset_union_right.trans hunion.subset
  have hCt : C ⊆ t := subset_union_right.trans hUnion.subset
  have hkeepc (x : c) : H ⟨x, hcs x.property⟩ =
      ⟨ec x, hCt (ec x).property⟩ := Subtype.ext (hH₀c x)
  refine ⟨H, hH, hkeep, H.mem_subset_iff_of_extension e hds hDt hkeep,
    H.mem_subset_iff_of_extension ec hcs hCt hkeepc, ?_⟩
  intro x
  rcases hunion.symm.subset x.property with hxd | hxc
  · have hx : (x : X) ∈ q ↔ (x : X) ∈ u := by
      rw [← houter]
      simp only [mem_inter_iff, hxd, true_and]
    have hy : (e ⟨x, hxd⟩ : Y) ∈ U ↔ (e ⟨x, hxd⟩ : Y) ∈ r := by
      rw [← hOuter]
      simp only [mem_inter_iff, (e ⟨x, hxd⟩).property, true_and]
    rw [congrArg (fun y : t => (y : Y)) (hkeep ⟨x, hxd⟩)]
    exact hx.trans ((hmemu ⟨x, hxd⟩).trans hy)
  · have hx : (x : X) ∈ q ↔ (x : X) ∈ v := by
      rw [← hcouter]
      simp only [mem_inter_iff, hxc, true_and]
    have hy : (ec ⟨x, hxc⟩ : Y) ∈ V ↔ (ec ⟨x, hxc⟩ : Y) ∈ r := by
      rw [← hCouter]
      exact and_iff_right (ec ⟨x, hxc⟩).property
    rw [congrArg (fun y : t => (y : Y)) (hkeepc ⟨x, hxc⟩)]
    exact hx.trans ((hecv ⟨x, hxc⟩).trans hy)

end Set
