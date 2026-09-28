import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRelativeAttachedDiskExtension

set_option autoImplicit false

open Set Geometry

namespace Set

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem IsFinitePLBallPair.exists_extension_of_two_attached_disks_and_boundary
    {s q : Set X} {t r : Set Y}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (ht : IsFinitePLBallPair (ℝ × ℝ) t r)
    (d u w : Bool → Set X) (D U W : Bool → Set Y)
    (a b : Bool → X) (A B : Bool → Y)
    (hd : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (d i) (u i ∪ w i))
    (hds : ∀ i, d i ⊆ s)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (U i ∪ W i))
    (hDt : ∀ i, D i ⊆ t)
    (hu : ∀ i, IsFinitePLBallPair ℝ (u i) {a i, b i}) (huq : ∀ i, u i ⊆ q)
    (hw : ∀ i, IsFinitePLBallPair ℝ (w i) {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hproper : ∀ i, w i \ {a i, b i} ⊆ s \ q)
    (hU : ∀ i, IsFinitePLBallPair ℝ (U i) {A i, B i}) (hUr : ∀ i, U i ⊆ r)
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {A i, B i}) (hAB : ∀ i, A i ≠ B i)
    (hProper : ∀ i, W i \ {A i, B i} ⊆ t \ r)
    (hdis : Disjoint (d false) (d true)) (hDis : Disjoint (D false) (D true))
    (e : ∀ i, d i ≃ₜ D i) (he : ∀ i, (e i).IsFinitePL)
    (hmemu : ∀ i (x : d i), (x : X) ∈ u i ↔ (e i x : Y) ∈ U i)
    (hmemw : ∀ i (x : d i), (x : X) ∈ w i ↔ (e i x : Y) ∈ W i)
    (bnd : q ≃ₜ r) (hbnd : bnd.IsFinitePL)
    (hagree : ∀ i (x : u i), (bnd ⟨x, huq i x.property⟩ : Y) =
      (e i ⟨x, (hd i).1 (Or.inl x.property)⟩ : Y)) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ i (x : d i), H ⟨x, hds i x.property⟩ = ⟨e i x, hDt i (e i x).property⟩) ∧
      (∀ x : q, H ⟨x, hs.1 x.property⟩ = ⟨bnd x, ht.1 (bnd x).property⟩) ∧
      (∀ i (x : s), (x : X) ∈ d i ↔ (H x : Y) ∈ D i) ∧
      ∀ x : s, (x : X) ∈ q ↔ (H x : Y) ∈ r := by
  obtain ⟨E, hE, hEd, hEq, hEdmem, hEqmem⟩ :=
    hs.exists_extension_of_attached_disk_and_boundary ht
      (hd false) (hds false) (hD false) (hDt false)
      (hu false) (huq false) (hw false) (hab false) (hproper false)
      (hU false) (hUr false) (hW false) (hAB false) (hProper false)
      (e false) (he false) (hmemu false) (hmemw false) bnd hbnd (hagree false)
  obtain ⟨v, hv, hq, _, hc, hunion, hinter, _, hcouter⟩ :=
    hs.exists_boundary_attached_disk_complement (hd false) (hds false)
      (hu false) (huq false) (hw false) (hab false) (hproper false)
  obtain ⟨V, hV, hr, _, hC, hUnion, hInter, _, hCouter⟩ :=
    ht.exists_boundary_attached_disk_complement (hD false) (hDt false)
      (hU false) (hUr false) (hW false) (hAB false) (hProper false)
  let c := s \ (d false \ w false)
  let C := t \ (D false \ W false)
  have hcs : c ⊆ s := sdiff_subset
  have hCt : C ⊆ t := sdiff_subset
  have hwd : w false ⊆ d false := subset_union_right.trans (hd false).1
  have hWD : W false ⊆ D false := subset_union_right.trans (hD false).1
  let ew := (e false).restrictSubsets hwd hWD (hmemw false)
  have hkeepw (x : w false) : E ⟨x, hds false (hwd x.property)⟩ =
      ⟨ew x, hDt false (hWD (ew x).property)⟩ := hEd ⟨x, hwd x.property⟩
  have hEw := E.mem_subset_iff_of_extension ew (hwd.trans (hds false))
    (hWD.trans (hDt false)) hkeepw
  have hEc (x : s) : (x : X) ∈ c ↔ (E x : Y) ∈ C := by
    change ((x : X) ∈ s ∧ ¬ ((x : X) ∈ d false ∧ (x : X) ∉ w false)) ↔
      ((E x : Y) ∈ t ∧ ¬ ((E x : Y) ∈ D false ∧ (E x : Y) ∉ W false))
    simp only [x.property, (E x).property, true_and, hEdmem x, hEw x]
  have hEv (x : s) : (x : X) ∈ v ↔ (E x : Y) ∈ V := by
    rw [← hcouter, ← hCouter]
    exact and_congr (hEc x) (hEqmem x)
  have hcb : w false ∪ v ⊆ s := hc.1.trans hcs
  have hCb : W false ∪ V ⊆ t := hC.1.trans hCt
  have hEb (x : s) : (x : X) ∈ w false ∪ v ↔ (E x : Y) ∈ W false ∪ V :=
    or_congr (hEw x) (hEv x)
  let bc := E.restrictSubsets hcb hCb hEb
  have hwcopy := hw false
  have hvcopy := hv
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJw, _⟩, _⟩, _⟩ := hwcopy
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLv, _⟩, _⟩, _⟩ := hvcopy
  obtain ⟨K, hK, hKb⟩ := J.exists_finite_triangulation_union L hJ hL
  rw [hJw, hLv] at hKb
  have hbc : bc.IsFinitePL := hE.restrictSubsets hcb hCb hEb K hK hKb
  have hd1c : d true ⊆ c := by
    intro x hx
    exact ⟨hds true hx, fun h => disjoint_left.mp hdis h.1 hx⟩
  have hD1C : D true ⊆ C := by
    intro x hx
    exact ⟨hDt true hx, fun h => disjoint_left.mp hDis h.1 hx⟩
  have hu1b : u true ⊆ w false ∪ v := by
    intro x hx
    exact Or.inr (hcouter.subset
      ⟨hd1c ((hd true).1 (Or.inl hx)), huq true hx⟩)
  have hU1b : U true ⊆ W false ∪ V := by
    intro x hx
    exact Or.inr (hCouter.subset
      ⟨hD1C ((hD true).1 (Or.inl hx)), hUr true hx⟩)
  have hp1 : w true \ {a true, b true} ⊆ c \ (w false ∪ v) := by
    intro x hx
    have hxd : x ∈ d true := (hd true).1 (Or.inr hx.1)
    refine ⟨hd1c hxd, ?_⟩
    rintro (hxw | hxv)
    · exact disjoint_left.mp hdis (hwd hxw) hxd
    · exact (hproper true hx).2 (hq.subset (Or.inr hxv))
  have hP1 : W true \ {A true, B true} ⊆ C \ (W false ∪ V) := by
    intro x hx
    have hxD : x ∈ D true := (hD true).1 (Or.inr hx.1)
    refine ⟨hD1C hxD, ?_⟩
    rintro (hxW | hxV)
    · exact disjoint_left.mp hDis (hWD hxW) hxD
    · exact (hProper true hx).2 (hr.subset (Or.inr hxV))
  have hagree1 (x : u true) : (bc ⟨x, hu1b x.property⟩ : Y) =
      (e true ⟨x, (hd true).1 (Or.inl x.property)⟩ : Y) :=
    (congrArg (fun y : t => (y : Y)) (hEq ⟨x, huq true x.property⟩)).trans
      (hagree true x)
  obtain ⟨ec, hec, hecd, hecb, _, _⟩ :=
    hc.exists_extension_of_attached_disk_and_boundary hC
      (hd true) hd1c (hD true) hD1C
      (hu true) hu1b (hw true) (hab true) hp1
      (hU true) hU1b (hW true) (hAB true) hP1
      (e true) (he true) (hmemu true) (hmemw true) bc hbc hagree1
  have hoverlap (x : d false) : (x : X) ∈ c ↔ (e false x : Y) ∈ C := by
    have hx : (x : X) ∈ c ↔ (x : X) ∈ w false := by
      rw [← hinter]
      simp only [c, mem_inter_iff, x.property, true_and]
    have hy : (e false x : Y) ∈ W false ↔ (e false x : Y) ∈ C := by
      rw [← hInter]
      simp only [C, mem_inter_iff, (e false x).property, true_and]
    exact hx.trans ((hmemw false x).trans hy)
  have hagree0 (x : X) (hxd : x ∈ d false) (hxc : x ∈ c) :
      (e false ⟨x, hxd⟩ : Y) = (ec ⟨x, hxc⟩ : Y) := by
    have hxw : x ∈ w false := hinter ▸ And.intro hxd hxc
    have hce : (ec ⟨x, hxc⟩ : Y) = (E ⟨x, hcs hxc⟩ : Y) :=
      congrArg (fun y : C => (y : Y)) (hecb ⟨x, Or.inl hxw⟩)
    exact (congrArg (fun y : t => (y : Y)) (hEd ⟨x, hxd⟩)).symm.trans hce.symm
  obtain ⟨H₀, hH₀, hH₀d, hH₀c⟩ :=
    Homeomorph.exists_union_finitePL (e false) ec (he false) hec hoverlap hagree0
  let H : s ≃ₜ t := (Homeomorph.setCongr hunion.symm).trans
    (H₀.trans (Homeomorph.setCongr hUnion))
  have hH : H.IsFinitePL := by
    obtain ⟨f, hf, hHf⟩ := hH₀
    rw [hunion] at hf
    exact ⟨f, hf, fun x => hHf ⟨x, hunion.symm ▸ x.property⟩⟩
  have hkeep (i : Bool) (x : d i) : H ⟨x, hds i x.property⟩ =
      ⟨e i x, hDt i (e i x).property⟩ := by
    apply Subtype.ext
    cases i with
    | false => exact hH₀d x
    | true =>
        exact (hH₀c ⟨x, hd1c x.property⟩).trans
          (congrArg (fun y : C => (y : Y)) (hecd x))
  have hkeepq (x : q) : H ⟨x, hs.1 x.property⟩ =
      ⟨bnd x, ht.1 (bnd x).property⟩ := by
    apply Subtype.ext
    rcases hq.symm.subset x.property with hxu | hxv
    · exact (hH₀d ⟨x, (hd false).1 (Or.inl hxu)⟩).trans (hagree false ⟨x, hxu⟩).symm
    · exact (hH₀c ⟨x, hc.1 (Or.inr hxv)⟩).trans
        ((congrArg (fun y : C => (y : Y)) (hecb ⟨x, Or.inr hxv⟩)).trans
          (congrArg (fun y : t => (y : Y)) (hEq x)))
  exact ⟨H, hH, hkeep, hkeepq,
    fun i => H.mem_subset_iff_of_extension (e i) (hds i) (hDt i) (hkeep i),
    H.mem_subset_iff_of_extension bnd hs.1 ht.1 hkeepq⟩

end Set
