import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ChosenHolePuncturedBall
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardPrism
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.DiskPortPuncturedBallSum

set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

open PoincareConjecture.M76.HamiltonIndexTwoStandard

theorem extend_actual_disk_port
    {V W E F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {B S d q : Set E} {T R D Q : Set F}
    (hB : IsFinitePLBallPair V B S) (hT : IsFinitePLBallPair W T R)
    (hV : Module.finrank ℝ V = 3) (hW : Module.finrank ℝ W = 3)
    (hd : IsFinitePLBallPair P2 d q) (hD : IsFinitePLBallPair P2 D Q)
    (hds : d ⊆ S) (hDR : D ⊆ R)
    (hout : (S \ d).Nonempty) (hOut : (R \ D).Nonempty)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (heq : ∀ x : d, (x : E) ∈ q ↔ (e x : F) ∈ Q) :
    ∃ H : B ≃ₜ T, H.IsFinitePL ∧
      (∀ x : d, (H ⟨x, hB.1 (hds x.property)⟩ : F) = e x) ∧
      (∀ x : B, (x : E) ∈ S ↔ (H x : F) ∈ R) ∧
      (∀ x : B, (x : E) ∈ d ↔ (H x : F) ∈ D) := by
  have hb := hB.boundary_disk_complement hV hd hds hout
  have hC := hT.boundary_disk_complement hW hD hDR hOut
  have hsrc : (S \ (d \ q)) ∪ d = S := by
    ext x
    have hx := @hds x
    simp only [mem_union, mem_sdiff]
    tauto
  have htgt : (R \ (D \ Q)) ∪ D = R := by
    ext x
    have hx := @hDR x
    simp only [mem_union, mem_sdiff]
    tauto
  have hi : (S \ (d \ q)) ∩ d = q := by
    ext x
    have hx := @hds x
    have hq := @hd.1 x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  have hI : (R \ (D \ Q)) ∩ D = Q := by
    ext x
    have hx := @hDR x
    have hq := @hD.1 x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  obtain ⟨G, hG, hkeep, _, hport⟩ :=
    hb.exists_union_homeomorph_of_boundary_piece hC hi hI e he heq
  let eb := (Homeomorph.setCongr hsrc.symm).trans
    (G.trans (Homeomorph.setCongr htgt))
  have heb : eb.IsFinitePL := hG.setCongr hsrc htgt
  obtain ⟨H, hH, hHb, hHS⟩ := hB.exists_extension hT eb heb
  have hHd (x : d) : H ⟨x, hB.1 (hds x.property)⟩ =
      ⟨e x, hT.1 (hDR (e x).property)⟩ := by
    apply Subtype.ext
    exact (congrArg (fun y : T => (y : F)) (hHb ⟨x, hds x.property⟩)).trans
      (congrArg (fun y : ((R \ (D \ Q)) ∪ D : Set F) => (y : F)) (hkeep x))
  exact ⟨H, hH, fun x => congrArg Subtype.val (hHd x), hHS,
    H.mem_subset_iff_of_extension e (hds.trans hB.1) (hDR.trans hT.1) hHd⟩

theorem exists_selected_hole_disk_port_normalization {ι : Type*}
    (a r : ι → Set V4) (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (haS : ∀ i, a i ⊆ sphere)
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a i \ r i)))
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) (i : ι)
    {d q : Set V4} (hd : IsFinitePLBallPair P2 d q)
    (hdr : d ⊆ r i) (hout : (r i \ d).Nonempty) :
    let B := sphere \ (a i \ r i)
    let S := (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
    ∃ (f : V4 → P3) (H : B ≃ₜ prism (-1) 0), H.IsFinitePL ∧
      FinitePiecewiseAffineOn f B ∧ InjOn f B ∧
      (∀ x : B, (H x : P3) = f x) ∧
      (∀ x : B, (x : V4) ∈ r i ↔ (H x : P3) ∈ S) ∧
      (∀ x : B, (x : V4) ∈ d ↔ (H x : P3) ∈ endDisk 0) ∧
      (∀ j : {j : ι // j ≠ i},
        IsFinitePLBallPair V3 (f '' a j) (f '' r j) ∧
        f '' a j ⊆ prism (-1) 0 \ S) ∧
      Pairwise (fun j k : {j : ι // j ≠ i} => Disjoint (f '' a j) (f '' a k)) ∧
      f '' (sphere \ ⋃ j, a j \ r j) =
        prism (-1) 0 \ ⋃ j : {j : ι // j ≠ i}, (f '' a j) \ (f '' r j) ∧
      (∀ j (x : B), (x : V4) ∈ r j ↔ (H x : P3) ∈ f '' r j) ∧
      ∀ x : B, (x : V4) ∈ q ↔ (H x : P3) ∈ endRim 0 := by
  dsimp only
  let B := sphere \ (a i \ r i)
  let S := (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
  obtain ⟨hB, hother, hpuncture, hrims⟩ :=
    selected_hole_punctured_ball a r ha haS hopen hdis i
  have hT := prism_ballPair (by norm_num : (-1 : ℝ) < 0)
  have hEnd := endDisk_ballPair 0
  obtain ⟨e, he, heq⟩ := hd.exists_homeomorph hEnd
  have hOut : (S \ endDisk 0).Nonempty := by
    refine ⟨((0, 0), -1), Or.inl (Or.inr ?_), ?_⟩
    · norm_num [endDisk, CoordinateHalfBoxes.base]
    · intro hx
      have hh : (-1 : ℝ) = 0 := hx.2
      norm_num at hh
  obtain ⟨H, hH, hkeep, hHS, hHd⟩ := extend_actual_disk_port hB hT
    (by simp) (by simp [Module.finrank_prod]) hd hEnd hdr subset_union_right
    hout hOut e he heq
  have hHcopy := hH
  obtain ⟨f, hf, hval⟩ := hHcopy
  have hfi : InjOn f B := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective
      (Subtype.ext ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hmarked (c : Set V4) (hc : c ⊆ B) (x : B) :
      (x : V4) ∈ c ↔ (H x : P3) ∈ f '' c := by
    rw [hval]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hfi (hc hy) x.property hyx ▸ hy
  have hrB (j : ι) : r j ⊆ B := fun x hx =>
    ⟨(hrims j hx).1, fun h => (hrims j hx).2 (mem_iUnion.mpr ⟨i, h⟩)⟩
  have hholes (j : {j : ι // j ≠ i}) :
      IsFinitePLBallPair V3 (f '' a j) (f '' r j) ∧
        f '' a j ⊆ prism (-1) 0 \ S := by
    refine ⟨(ha j).image_of_subset hf ((hother j).trans sdiff_subset) hfi, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hfx := hval ⟨x, (hother j hx).1⟩
    refine ⟨hfx ▸ (H ⟨x, (hother j hx).1⟩).property, ?_⟩
    intro hs
    exact (hother j hx).2 ((hHS ⟨x, (hother j hx).1⟩).mpr (hfx.symm ▸ hs))
  have hHq (x : B) : (x : V4) ∈ q ↔ (H x : P3) ∈ endRim 0 := by
    by_cases hx : (x : V4) ∈ d
    · rw [hkeep ⟨x, hx⟩]
      exact heq ⟨x, hx⟩
    · constructor
      · exact fun hq => False.elim (hx (hd.1 hq))
      · exact fun hq => False.elim (hx ((hHd x).mpr (hEnd.1 hq)))
  refine ⟨f, H, hH, hf, hfi, hval, hHS, hHd, hholes, ?_, ?_,
    (fun j x => hmarked (r j) (hrB j) x), hHq⟩
  · intro j k hjk
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := hfi (hother j hx).1 (hother k hz).1 (hxy.trans hzy.symm)
    exact disjoint_left.mp (hdis (Subtype.val_injective.ne hjk)) hx (hxz.symm ▸ hz)
  · rw [← hpuncture]
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨(hval ⟨x, hx.1⟩) ▸ (H ⟨x, hx.1⟩).property, ?_⟩
      intro hh
      obtain ⟨j, ⟨y, hy, hyx⟩, hnr⟩ := mem_iUnion.mp hh
      have hyx' := hfi (hother j hy).1 hx.1 hyx
      exact hx.2 (mem_iUnion.mpr ⟨j, hyx' ▸ hy, fun hr => hnr ⟨x, hr, rfl⟩⟩)
    · intro y hy
      let x := H.symm ⟨y, hy.1⟩
      have hxy : f x = y := (hval x).symm.trans (congrArg Subtype.val (H.apply_symm_apply _))
      refine ⟨x, ⟨x.property, ?_⟩, hxy⟩
      intro hh
      obtain ⟨j, hja, hjr⟩ := mem_iUnion.mp hh
      apply hy.2
      refine mem_iUnion.mpr ⟨j, ⟨x, hja, hxy⟩, ?_⟩
      rintro ⟨z, hz, hzy⟩
      exact hjr (hfi (hrB j hz) x.property (hzy.trans hxy.symm) ▸ hz)

theorem exists_paired_selected_hole_disk_port_normalization {ι : Type*}
    (a r : Bool → ι → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : Bool → ι)
    {d q : Set V4} (hd : IsFinitePLBallPair P2 d q)
    (hdr : ∀ b, d ⊆ r b (i b)) (hout : ∀ b, (r b (i b) \ d).Nonempty) :
    let B := fun b => sphere \ (a b (i b) \ r b (i b))
    let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
    let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
      else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
    ∃ (f : Bool → V4 → P3) (H : ∀ b, B b ≃ₜ P b),
      (∀ b, (H b).IsFinitePL ∧ FinitePiecewiseAffineOn (f b) (B b) ∧
        InjOn (f b) (B b) ∧ (∀ x : B b, (H b x : P3) = f b x) ∧
        (∀ x : B b, (x : V4) ∈ r b (i b) ↔ (H b x : P3) ∈ S b) ∧
        (∀ x : B b, (x : V4) ∈ d ↔ (H b x : P3) ∈ endDisk 0)) ∧
      EqOn (f false) (f true) d ∧
      (f false '' B false) ∩ (f true '' B true) = endDisk 0 ∧
      (∀ b (j : {j : ι // j ≠ i b}),
        IsFinitePLBallPair V3 (f b '' a b j) (f b '' r b j) ∧
        f b '' a b j ⊆ P b \ S b) ∧
      (∀ b, Pairwise fun j k : {j : ι // j ≠ i b} =>
        Disjoint (f b '' a b j) (f b '' a b k)) ∧
      ∀ (j : {j : ι // j ≠ i false}) (k : {j : ι // j ≠ i true}),
        Disjoint (f false '' a false j) (f true '' a true k) := by
  dsimp only
  let B := fun b => sphere \ (a b (i b) \ r b (i b))
  let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
  let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
    else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
  have hB (b : Bool) :=
    selected_hole_punctured_ball (a b) (r b) (ha b) (haS b) (hopen b) (hdis b) (i b)
  obtain ⟨f₀, H₀, hH₀, hf₀, hfi₀, hval₀, hS₀, hd₀, _, _, _, _, hq₀⟩ :=
    exists_selected_hole_disk_port_normalization (a false) (r false) (ha false)
      (haS false) (hopen false) (hdis false) (i false) hd (hdr false) (hout false)
  have hdB₀ := (hdr false).trans (hB false).1.1
  have hdP₀ : endDisk 0 ⊆ prism (-1) 0 :=
    subset_union_right.trans (prism_ballPair (by norm_num : (-1 : ℝ) < 0)).1
  let e := H₀.restrictSubsets hdB₀ hdP₀ hd₀
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Kd, hKd, hKdd, _⟩, _⟩, _⟩ := hdcopy
  have he : e.IsFinitePL := hH₀.restrictSubsets hdB₀ hdP₀ hd₀ Kd hKd hKdd
  have heq : ∀ x : d, (x : V4) ∈ q ↔ (e x : P3) ∈ endRim 0 := by
    exact fun x => hq₀ ⟨x, hdB₀ x.property⟩
  have hT := prism_ballPair (by norm_num : (0 : ℝ) < 1)
  have hdP₁ : endDisk 0 ⊆ (band 0 1 ∪ endDisk 0) ∪ endDisk 1 :=
    subset_union_right.trans subset_union_left
  have hOut : (((band 0 1 ∪ endDisk 0) ∪ endDisk 1) \ endDisk 0).Nonempty := by
    refine ⟨((0, 0), 1), Or.inr ?_, ?_⟩
    · norm_num [endDisk, CoordinateHalfBoxes.base]
    · intro hx
      have hh : (1 : ℝ) = 0 := hx.2
      norm_num at hh
  obtain ⟨H₁, hH₁, hkeep₁, hS₁, hd₁⟩ := extend_actual_disk_port (hB true).1 hT
    (by simp) (by simp [Module.finrank_prod]) hd (endDisk_ballPair 0)
    (hdr true) hdP₁ (hout true) hOut e he heq
  have hH₁copy := hH₁
  obtain ⟨f₁, hf₁, hval₁⟩ := hH₁copy
  have hfi₁ : InjOn f₁ (B true) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H₁.injective
      (Subtype.ext ((hval₁ ⟨x, hx⟩).trans (hxy.trans (hval₁ ⟨y, hy⟩).symm))))
  let f : Bool → V4 → P3 := fun b => if b then f₁ else f₀
  let H : ∀ b, B b ≃ₜ P b := fun b => by cases b; exact H₀; exact H₁
  have hmaps (b : Bool) :
      (H b).IsFinitePL ∧ FinitePiecewiseAffineOn (f b) (B b) ∧
        InjOn (f b) (B b) ∧ (∀ x : B b, (H b x : P3) = f b x) ∧
        (∀ x : B b, (x : V4) ∈ r b (i b) ↔ (H b x : P3) ∈ S b) ∧
        (∀ x : B b, (x : V4) ∈ d ↔ (H b x : P3) ∈ endDisk 0) := by
    cases b
    · exact ⟨hH₀, hf₀, hfi₀, hval₀, hS₀, hd₀⟩
    · exact ⟨hH₁, hf₁, hfi₁, hval₁, hS₁, hd₁⟩
  have himage (b : Bool) : f b '' B b = P b := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmaps b).2.2.2.1 ⟨x, hx⟩ ▸ (H b ⟨x, hx⟩).property
    · intro y hy
      let x := (H b).symm ⟨y, hy⟩
      exact ⟨x, x.property, ((hmaps b).2.2.2.1 x).symm.trans
        (congrArg Subtype.val ((H b).apply_symm_apply _))⟩
  have hinter : P false ∩ P true = endDisk 0 := by
    ext x
    change ((x.1 ∈ CoordinateHalfBoxes.base 1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∧
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1)) ↔
      x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = 0
    constructor
    · intro hx
      exact ⟨hx.1.1, le_antisymm hx.1.2.2 hx.2.2.1⟩
    · rintro ⟨hx, heq⟩
      rw [heq]
      exact ⟨⟨hx, by norm_num⟩, hx, by norm_num⟩
  have hholes (b : Bool) (j : {j : ι // j ≠ i b}) :
      IsFinitePLBallPair V3 (f b '' a b j) (f b '' r b j) ∧
        f b '' a b j ⊆ P b \ S b := by
    have hj := (hB b).2.1 j
    refine ⟨(ha b j).image_of_subset (hmaps b).2.1 (hj.trans sdiff_subset)
      (hmaps b).2.2.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hv := (hmaps b).2.2.2.1 ⟨x, (hj hx).1⟩
    refine ⟨hv ▸ (H b ⟨x, (hj hx).1⟩).property, ?_⟩
    intro hs
    exact (hj hx).2 (((hmaps b).2.2.2.2.1 _).mpr (hv.symm ▸ hs))
  refine ⟨f, H, hmaps, ?_, ?_, hholes, ?_, ?_⟩
  · intro x hx
    exact (hval₀ ⟨x, hdB₀ hx⟩).symm.trans
      ((hkeep₁ ⟨x, hx⟩).symm.trans (hval₁ ⟨x, (hB true).1.1 (hdr true hx)⟩))
  · rw [himage false, himage true, hinter]
  · intro b j k hjk
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := (hmaps b).2.2.1 ((hB b).2.1 j hx).1 ((hB b).2.1 k hz).1
      (hxy.trans hzy.symm)
    exact disjoint_left.mp (hdis b (Subtype.val_injective.ne hjk)) hx (hxz.symm ▸ hz)
  · intro j k
    apply disjoint_left.mpr
    intro x hx hz
    have hport := hinter.subset ⟨((hholes false j).2 hx).1, ((hholes true k).2 hz).1⟩
    exact ((hholes false j).2 hx).2 (Or.inr hport)

theorem exists_selected_hole_disk_port_sum {ι : Type*} [Finite ι]
    (a r : Bool → ι → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : Bool → ι)
    {d q : Set V4} (hd : IsFinitePLBallPair P2 d q)
    (hdr : ∀ b, d ⊆ r b (i b)) (hout : ∀ b, (r b (i b) \ d).Nonempty) :
    let B := fun b => sphere \ (a b (i b) \ r b (i b))
    let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
    let J := (b : Bool) × {j : ι // j ≠ i b}
    ∃ (f : Bool → V4 → P3) (H : ∀ b, B b ≃ₜ P b),
      (∀ b, (H b).IsFinitePL ∧ FinitePiecewiseAffineOn (f b) (B b) ∧
        InjOn (f b) (B b) ∧ (∀ x : B b, (H b x : P3) = f b x) ∧
        (∀ x : B b, (x : V4) ∈ r b (i b) ↔ (H b x : P3) ∈
          (if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
            else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0)) ∧
        (∀ x : B b, (x : V4) ∈ d ↔ (H b x : P3) ∈ endDisk 0)) ∧
      EqOn (f false) (f true) d ∧
      let c : J → Set P3 := fun j => f j.1 '' a j.1 j.2
      let t : J → Set P3 := fun j => f j.1 '' r j.1 j.2
      ∃ g : P3 → V4,
        (∀ j, IsFinitePLBallPair V3 (g '' c j) (g '' t j)) ∧
        (∀ j, g '' c j ⊆ lower \ seam) ∧
        (∀ j, Disjoint upper (g '' c j)) ∧
        Pairwise (fun j k => Disjoint (g '' c j) (g '' c k)) ∧
        let p := (prism (-1) 0 ∪ prism 0 1) \ ⋃ j, c j \ t j
        let T := sphere \ ((upper \ seam) ∪ ⋃ j, (g '' c j) \ (g '' t j))
        ∃ (L : SimplicialComplex ℝ P3) (F : p ≃ₜ T),
          L.faces.Finite ∧ L.space = p ∧ F.IsFinitePL ∧
          (∀ x : p, (F x : V4) = g x) ∧
          (∀ j (x : p), (x : P3) ∈ t j ↔ (F x : V4) ∈ g '' t j) ∧
          ∀ j, (fun x : p => (F x : V4)) ''
            ((Subtype.val : p → P3) ⁻¹' t j) = g '' t j := by
  dsimp only
  let B := fun b => sphere \ (a b (i b) \ r b (i b))
  let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
  let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
    else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
  let J := (b : Bool) × {j : ι // j ≠ i b}
  obtain ⟨f, H, hmaps, hagree, _, hholes, hpair, hcross⟩ :=
    exists_paired_selected_hole_disk_port_normalization a r ha haS hopen hdis i hd hdr hout
  let c : J → Set P3 := fun j => f j.1 '' a j.1 j.2
  let t : J → Set P3 := fun j => f j.1 '' r j.1 j.2
  have hc (j : J) : IsFinitePLBallPair V3 (c j) (t j) := (hholes j.1 j.2).1
  have hside (j : J) : c j ⊆ prism (-1) 0 \ S false ∨
      c j ⊆ prism 0 1 \ S true := by
    rcases j with ⟨b, j⟩
    cases b
    · exact Or.inl (hholes false j).2
    · exact Or.inr (hholes true j).2
  have hcdis : Pairwise fun j k : J => Disjoint (c j) (c k) := by
    rintro ⟨b, j⟩ ⟨b', k⟩ hne
    cases b <;> cases b'
    · exact hpair false (fun hjk => hne (by cases hjk; rfl))
    · exact hcross j k
    · exact (hcross k j).symm
    · exact hpair true (fun hjk => hne (by cases hjk; rfl))
  have hBU : prism (-1) 0 ∩ prism 0 1 = endDisk 0 := by
    ext x
    change ((x.1 ∈ CoordinateHalfBoxes.base 1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∧
      (x.1 ∈ CoordinateHalfBoxes.base 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1)) ↔
      x.1 ∈ CoordinateHalfBoxes.base 1 ∧ x.2 = 0
    constructor
    · intro hx
      exact ⟨hx.1.1, le_antisymm hx.1.2.2 hx.2.2.1⟩
    · rintro ⟨hx, heq⟩
      rw [heq]
      exact ⟨⟨hx, by norm_num⟩, hx, by norm_num⟩
  have hout₀ : (S false \ endDisk 0).Nonempty := by
    refine ⟨((0, 0), -1), Or.inl (Or.inr ?_), ?_⟩
    · norm_num [endDisk, CoordinateHalfBoxes.base]
    · intro hx
      have hh : (-1 : ℝ) = 0 := hx.2
      norm_num at hh
  have hout₁ : (S true \ endDisk 0).Nonempty := by
    refine ⟨((0, 0), 1), Or.inr ?_, ?_⟩
    · norm_num [endDisk, CoordinateHalfBoxes.base]
    · intro hx
      have hh : (1 : ℝ) = 0 := hx.2
      norm_num at hh
  obtain ⟨_, g, _, _, _, _, hgball, hgin, hgout, hgdis,
      L, F, hL, hLs, hF, hFval, hFrim, hFrimimage, _⟩ :=
    (prism_ballPair (by norm_num : (-1 : ℝ) < 0)).exists_punctured_sphere_of_disk_port_sum
      (prism_ballPair (by norm_num : (0 : ℝ) < 1)) (endDisk_ballPair 0)
      subset_union_right (subset_union_right.trans subset_union_left) hout₀ hout₁
      hBU c t hc hside hcdis
  exact ⟨f, H, hmaps, hagree, g, hgball, hgin, hgout, hgdis,
    L, F, hL, hLs, hF, hFval, hFrim, hFrimimage⟩

end Set
