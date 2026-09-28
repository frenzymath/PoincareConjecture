import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.FourArcRectangle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualOwnerArcs

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_split_interval_at
    {s : Set E} {a b c : E}
    (hs : IsFinitePLBallPair ℝ s {a, c})
    (hb : b ∈ s) (hac : a ≠ c) (hab : a ≠ b) (hbc : b ≠ c) :
    ∃ W R : Set E,
      IsFinitePLBallPair ℝ W {a, b} ∧
      IsFinitePLBallPair ℝ R {b, c} ∧
      W ∪ R = s ∧ W ∩ R = {b} ∧ c ∉ W ∧ a ∉ R := by
  obtain ⟨e, he, hea, hec⟩ :=
    hs.exists_unitInterval_chart_with_endpoints hac
  obtain ⟨f, hf, hfe⟩ := he
  let α : ℝ := (e.symm ⟨b, hb⟩ : ℝ)
  have hαmem : α ∈ Icc (0 : ℝ) 1 := (e.symm ⟨b, hb⟩).property
  have hα0 : 0 < α := by
    by_contra h
    have hzero : α = 0 := le_antisymm (le_of_not_gt h) hαmem.1
    have hf0 : f 0 = a := (hfe ⟨0, by simp⟩).symm.trans hea
    have hfb : f α = b := (hfe ⟨α, hαmem⟩).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩))
    exact hab (hf0.symm.trans (hzero ▸ hfb))
  have hα1 : α < 1 := by
    by_contra h
    have hone : α = 1 := le_antisymm hαmem.2 (le_of_not_gt h)
    have hf1 : f 1 = c := (hfe ⟨1, by simp⟩).symm.trans hec
    have hfb : f α = b := (hfe ⟨α, hαmem⟩).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩))
    exact hbc ((hone ▸ hfb).symm.trans hf1)
  have hf0 : f 0 = a := (hfe ⟨0, by simp⟩).symm.trans hea
  have hf1 : f 1 = c := (hfe ⟨1, by simp⟩).symm.trans hec
  have hfin : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) := hf
  have hinj : InjOn f (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hfe ⟨x, hx⟩).trans (hxy.trans (hfe ⟨y, hy⟩).symm))))
  let W := f '' Icc (0 : ℝ) α
  let R := f '' Icc α 1
  have hleft : Icc (0 : ℝ) α ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hαmem.2⟩
  have hright : Icc α 1 ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hαmem.1.trans hx.1, hx.2⟩
  have hW : IsFinitePLBallPair ℝ W {a, b} := by
    have h := (isFinitePLBallPair_Icc hα0).image_of_subset hfin hleft hinj
    have hf0 : f 0 = a := (hfe ⟨0, by simp⟩).symm.trans hea
    have hfb : f α = b := (hfe ⟨α, hαmem⟩).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩))
    simpa only [W, image_pair, hf0, hfb] using h
  have hR : IsFinitePLBallPair ℝ R {b, c} := by
    have h := (isFinitePLBallPair_Icc hα1).image_of_subset hfin hright hinj
    have hf1 : f 1 = c := (hfe ⟨1, by simp⟩).symm.trans hec
    have hfb : f α = b := (hfe ⟨α, hαmem⟩).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩))
    simpa only [R, image_pair, hfb, hf1] using h
  have himage : f '' Icc (0 : ℝ) 1 = s := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact hfe ⟨t, ht⟩ ▸ (e ⟨t, ht⟩).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).property, ?_⟩
      exact (hfe _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  have hcover : (Icc (0 : ℝ) α : Set ℝ) ∪ Icc α 1 = Icc (0 : ℝ) 1 :=
    Icc_union_Icc_eq_Icc hα0.le hα1.le
  have hinter : (Icc (0 : ℝ) α : Set ℝ) ∩ Icc α 1 = ({α} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      exact le_antisymm ht.1.2 ht.2.1
    · rintro rfl
      exact ⟨⟨hαmem.1, le_rfl⟩, ⟨le_rfl, hαmem.2⟩⟩
  have hcW : c ∉ W := by
    rintro ⟨t, ht, hft⟩
    have ht1 : t = 1 := hinj (hleft ht)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (hft.trans hf1.symm)
    exact (not_le_of_gt hα1) (ht1 ▸ ht.2)
  have haR : a ∉ R := by
    rintro ⟨t, ht, hft⟩
    have ht0 : t = 0 := hinj (hright ht)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (hft.trans hf0.symm)
    exact (not_le_of_gt hα0) (ht0 ▸ ht.1)
  refine ⟨W, R, hW, hR, ?_, ?_, hcW, haR⟩
  · rw [← image_union, hcover, himage]
  · have hmap := image_inter_on (s := Icc (0 : ℝ) α) (t := Icc α 1)
      (fun x hx y hy hxy => hinj (hright hx) (hleft hy) hxy)
    rw [← hmap, hinter, image_singleton]
    exact congrArg (fun x : E => ({x} : Set E)) ((hfe ⟨α, hαmem⟩).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)))

private theorem exists_interior_boundary_mark
    {s : Set E} {a b : E} (hs : IsFinitePLBallPair ℝ s {a, b})
    (hab : a ≠ b) :
    ∃ c : E, c ∈ s ∧ c ≠ a ∧ c ≠ b := by
  obtain ⟨e, _, hea, heb⟩ := hs.exists_unitInterval_chart_with_endpoints hab
  let m : Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  refine ⟨e m, (e m).property, ?_, ?_⟩
  · intro h
    have heq : e m = e 0 := Subtype.ext (h.trans hea.symm)
    have hm : m = (0 : Icc (0 : ℝ) 1) := e.injective heq
    have hv := congrArg Subtype.val hm
    norm_num [m] at hv
  · intro h
    have heq : e m = e 1 := Subtype.ext (h.trans heb.symm)
    have hm : m = (1 : Icc (0 : ℝ) 1) := e.injective heq
    have hv := congrArg Subtype.val hm
    norm_num [m] at hv

theorem exists_marked_boundary_rectangle
    {D B : Set E} (hball : IsFinitePLBallPair (ℝ × ℝ) D B)
    {a b : E} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    ∃ c d : E, ∃ W Z L R : Set E,
      c ∈ B ∧ d ∈ B ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
      IsFinitePLBallPair ℝ W {a, c} ∧
      IsFinitePLBallPair ℝ Z {d, b} ∧
      IsFinitePLBallPair ℝ L {a, d} ∧
      IsFinitePLBallPair ℝ R {c, b} ∧
      ((W ∪ Z) ∪ (L ∪ R)) = B ∧ Disjoint W Z ∧ Disjoint L R ∧
      W ∩ L = {a} ∧ W ∩ R = {c} ∧ Z ∩ L = {d} ∧ Z ∩ R = {b} ∧
      ∃ C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ D,
        C.IsFinitePL ∧
        (∀ x, (C x : E) ∈ W ↔ (x : ℝ × ℝ).2 = 0) ∧
        (∀ x, (C x : E) ∈ Z ↔ (x : ℝ × ℝ).2 = 1) ∧
        (∀ x, (C x : E) ∈ L ↔ (x : ℝ × ℝ).1 = 0) ∧
        (∀ x, (C x : E) ∈ R ↔ (x : ℝ × ℝ).1 = 1) := by
  obtain ⟨U, V, hU, hV, hUV, hUVinter⟩ :=
    hball.exists_boundary_arcs ha hb hab
  obtain ⟨c, hc, hca, hcb⟩ := exists_interior_boundary_mark hU hab
  obtain ⟨d, hd, hda, hdb⟩ := exists_interior_boundary_mark hV hab
  obtain ⟨W, R, hW, hR, hWRim, hWRint, hWb, hRa⟩ :=
    exists_split_interval_at hU hc hab hca.symm hcb
  obtain ⟨L, Z, hL, hZ, hLZim, hLZint, hLb, hZa⟩ :=
    exists_split_interval_at hV hd hab hda.symm hdb
  have hWsub : W ⊆ U := by
    intro x hx
    rw [← hWRim]
    exact Or.inl hx
  have hRsub : R ⊆ U := by
    intro x hx
    rw [← hWRim]
    exact Or.inr hx
  have hLsub : L ⊆ V := by
    intro x hx
    rw [← hLZim]
    exact Or.inl hx
  have hZsub : Z ⊆ V := by
    intro x hx
    rw [← hLZim]
    exact Or.inr hx
  have hcross (x : E) (hxU : x ∈ U) (hxV : x ∈ V) :
      x = a ∨ x = b := by
    have hx := hUVinter.subset ⟨hxU, hxV⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using hx
  have hWZ : Disjoint W Z := by
    apply disjoint_left.mpr
    intro x hxW hxZ
    rcases hcross x (hWsub hxW) (hZsub hxZ) with rfl | rfl
    · exact hZa hxZ
    · exact hWb hxW
  have hLR : Disjoint L R := by
    apply disjoint_left.mpr
    intro x hxL hxR
    rcases hcross x (hRsub hxR) (hLsub hxL) with rfl | rfl
    · exact hRa hxR
    · exact hLb hxL
  have hWL : W ∩ L = {a} := by
    apply Subset.antisymm
    · intro x hx
      rcases hcross x (hWsub hx.1) (hLsub hx.2) with rfl | rfl
      · simp
      · exact (hWb hx.1).elim
    · intro x hx
      have hxa : x = a := by simpa using hx
      subst x
      exact ⟨hW.1 (by simp), hL.1 (by simp)⟩
  have hWR : W ∩ R = {c} := hWRint
  have hZL : Z ∩ L = {d} := by
    rw [inter_comm]
    exact hLZint
  have hZR : Z ∩ R = {b} := by
    apply Subset.antisymm
    · intro x hx
      rcases hcross x (hRsub hx.2) (hZsub hx.1) with rfl | rfl
      · exact (hZa hx.1).elim
      · simp
    · intro x hx
      have hxb : x = b := by simpa using hx
      subst x
      exact ⟨hZ.1 (by simp), hR.1 (by simp)⟩
  have hboundary : (W ∪ Z) ∪ (L ∪ R) = B := by
    have hparts : (W ∪ Z) ∪ (L ∪ R) = U ∪ V := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hx with (hx | hx) | (hx | hx)
        · exact Or.inl (hWsub hx)
        · exact Or.inr (hZsub hx)
        · exact Or.inr (hLsub hx)
        · exact Or.inl (hRsub hx)
      · intro x hx
        rcases hx with hx | hx
        · rcases (show x ∈ W ∪ R from hWRim ▸ hx) with hx | hx
          · exact Or.inl (Or.inl hx)
          · exact Or.inr (Or.inr hx)
        · rcases (show x ∈ L ∪ Z from hLZim ▸ hx) with hx | hx
          · exact Or.inr (Or.inl hx)
          · exact Or.inl (Or.inr hx)
    exact hparts.trans hUV
  obtain ⟨C, hC, hCW, hCZ, hCL, hCR⟩ :=
    exists_four_arc_rectangle
      (hboundary ▸ hball) hW hZ hL hR hca.symm hdb hda.symm hcb hWZ hLR hWL hWR hZL hZR
  have hcB : c ∈ B := by rw [← hUV]; exact Or.inl hc
  have hdB : d ∈ B := by rw [← hUV]; exact Or.inr hd
  exact ⟨c, d, W, Z, L, R, hcB, hdB, hca, hcb, hda, hdb,
    hW, hZ, hL, hR, hboundary, hWZ, hLR, hWL, hWR, hZL, hZR,
    C, hC, hCW, hCZ, hCL, hCR⟩

theorem exists_marked_boundary_rectangle_of_owner_interval
    {J : SimplicialComplex ℝ E} [Fintype J.faces]
    {S : Set J.vertices} {v₀ v₁ : J.vertices}
    {D B : Set E} (hball : IsFinitePLBallPair (ℝ × ℝ) D B)
    (hB : J.vertexDualRim S = B)
    (h : ownerIntervalStatement J S v₀ v₁) :
    ∃ a b c d : E, ∃ W Z L R : Set E,
      a ∈ B ∧ b ∈ B ∧ c ∈ B ∧ d ∈ B ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
      IsFinitePLBallPair ℝ W {a, c} ∧
      IsFinitePLBallPair ℝ Z {d, b} ∧
      IsFinitePLBallPair ℝ L {a, d} ∧
      IsFinitePLBallPair ℝ R {c, b} ∧
      ((W ∪ Z) ∪ (L ∪ R)) = B ∧ Disjoint W Z ∧ Disjoint L R ∧
      W ∩ L = {a} ∧ W ∩ R = {c} ∧ Z ∩ L = {d} ∧ Z ∩ R = {b} ∧
      ∃ C : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ D,
        C.IsFinitePL ∧
        (∀ x, (C x : E) ∈ W ↔ (x : ℝ × ℝ).2 = 0) ∧
        (∀ x, (C x : E) ∈ Z ↔ (x : ℝ × ℝ).2 = 1) ∧
        (∀ x, (C x : E) ∈ L ↔ (x : ℝ × ℝ).1 = 0) ∧
        (∀ x, (C x : E) ∈ R ↔ (x : ℝ × ℝ).1 = 1) := by
  rcases h with ⟨t, ht, u, hu, _, _, _, _, hcent, hpair, _, _, hrim⟩
  have ha : (t.centroid ℝ id) ∈ B := by
    rw [← hB]
    exact hrim (hpair.1 (by simp))
  have hb : (u.centroid ℝ id) ∈ B := by
    rw [← hB]
    exact hrim (hpair.1 (by simp))
  obtain ⟨c, d, W, Z, L, R, hcB, hdB, hca, hcb, hda, hdb,
      hW, hZ, hL, hR, hboundary, hWZ, hLR, hWL, hWR, hZL, hZR,
      C, hC, hCW, hCZ, hCL, hCR⟩ :=
    exists_marked_boundary_rectangle hball ha hb hcent
  exact ⟨t.centroid ℝ id, u.centroid ℝ id, c, d, W, Z, L, R,
    ha, hb, hcB, hdB, hca, hcb, hda, hdb, hW, hZ, hL, hR,
    hboundary, hWZ, hLR, hWL, hWR, hZL, hZR, C, hC, hCW, hCZ, hCL, hCR⟩

end PoincareConjecture.M76.PeriodicSquare
