import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.Isotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.BoundaryGerm.Gap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

theorem compact_ribbon_meets_disjoint_disks_only_on_edges
    (A : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1))
    (R : E2 → E2) (hR : Continuous R) (a : Real)
    (hstart : ∀ s ∈ Icc (-a) a,
      R (WithLp.toLp 2 ![s, 0]) ∈ A 0 '' closedBall (0 : E2) 1)
    (hfinish : ∀ s ∈ Icc (-a) a,
      R (WithLp.toLp 2 ![s, 1]) ∈ A 1 '' closedBall (0 : E2) 1)
    (havoid : ∀ s ∈ Icc (-a) a,
      Disjoint ((fun t : Real => R (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
        (frontier (A 0 '' closedBall 0 1) ∪ frontier (A 1 '' closedBall 0 1))) :
    let P := (fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-a) a ×ˢ Icc 0 1)
    IsCompact P ∧ ∀ i : Fin 2, (A i '' closedBall 0 1) ∩ P ⊆
      (fun s : Real => R (WithLp.toLp 2 ![s, (i : Real)])) '' Icc (-a) a := by
  have hout (s : Real) (hs : s ∈ Icc (-a) a) :=
    connector_image_subset_compl_of_disjoint_closed
      ((isCompact_closedBall _ _).image (A 0).continuous).isClosed
      ((isCompact_closedBall _ _).image (A 1).continuous).isClosed hA
      ((hR.comp (by fun_prop : Continuous (fun t : Real =>
        (WithLp.toLp 2 ![s, t] : E2))))).continuousOn
      (hstart s hs) (hfinish s hs) (havoid s hs)
  refine ⟨(isCompact_Icc.prod isCompact_Icc).image (hR.comp (by fun_prop)), ?_⟩
  rintro i x ⟨hx, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩⟩
  fin_cases i
  · by_cases ht0 : t = 0
    · subst t
      exact ⟨s, hs, by norm_num⟩
    · by_cases ht1 : t = 1
      · subst t
        exact (disjoint_left.mp hA hx (hfinish s hs)).elim
      · have hti : t ∈ Ioo 0 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
          lt_of_le_of_ne ht.2 ht1⟩
        exact (hout s hs (mem_image_of_mem _ hti) (Or.inl hx)).elim
  · by_cases ht1 : t = 1
    · subst t
      exact ⟨s, hs, by norm_num⟩
    · by_cases ht0 : t = 0
      · subst t
        exact (disjoint_left.mp hA (hstart s hs) hx).elim
      · have hti : t ∈ Ioo 0 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
          lt_of_le_of_ne ht.2 ht1⟩
        exact (hout s hs (mem_image_of_mem _ hti) (Or.inr hx)).elim

theorem exists_supported_disjoint_disk_pair_isotopy_away_closed_region
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : Disjoint (A 0 '' closedBall 0 1) (A 1 '' closedBall 0 1))
    (hB : Disjoint (B 0 '' closedBall 0 1) (B 1 '' closedBall 0 1))
    {r : Real} (hr : 1 < r)
    (f g : Fin 2 → E1 → S1)
    (hfi : ∀ i, InjOn (f i) (closedBall 0 r))
    (hfl : ∀ i x, x ∈ closedBall (0 : E1) r →
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ (f i) x)
    (hgi : ∀ i, InjOn (g i) (closedBall 0 r))
    (hgl : ∀ i x, x ∈ closedBall (0 : E1) r →
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ (g i) x)
    (hmark : ∀ i x, x ∈ closedBall (0 : E1) r → A i (f i x) = B i (g i x))
    (V : Fin 2 → Set E2) (hV : ∀ i, IsOpen (V i))
    (hmarkV : ∀ i, (fun x => A i (f i x)) '' closedBall (0 : E1) r ⊆ V i)
    (hside : ∀ i, V i ∩ (A i '' closedBall 0 1) = V i ∩ (B i '' closedBall 0 1))
    (P : Set E2) (hP : IsClosed P)
    (hAP : ∀ i, (A i '' closedBall 0 1) ∩ P ⊆
      (fun x => A i (f i x)) '' closedBall (0 : E1) 1)
    (hBP : ∀ i, (B i '' closedBall 0 1) ∩ P ⊆
      (fun x => A i (f i x)) '' closedBall (0 : E1) 1) :
    ∃ K : Set E2, IsCompact K ∧ Disjoint K P ∧
      (∀ i, Disjoint K ((fun x => A i (f i x)) '' closedBall (0 : E1) 1)) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        (∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧ P ⊆ U ∧ ∀ t, EqOn (Φ t) id U := by
  let L : Set E2 := (fun x => A 1 (f 1 x)) '' closedBall (0 : E1) r
  have hfcont : ContinuousOn (fun x => A 1 (f 1 x)) (closedBall (0 : E1) r) :=
    (A 1).continuous.comp_continuousOn (continuous_subtype_val.comp_continuousOn
      (fun x hx => (hfl 1 x hx).contMDiffAt.continuousAt.continuousWithinAt))
  have hL : IsCompact L := (isCompact_closedBall _ _).image_of_continuousOn hfcont
  have hLA : L ⊆ A 1 '' closedBall 0 1 := by
    rintro _ ⟨x, _, rfl⟩
    exact mem_image_of_mem (A 1) (sphere_subset_closedBall (f 1 x).property)
  have hLB : L ⊆ B 1 '' closedBall 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change A 1 (f 1 x) ∈ B 1 '' closedBall 0 1
    rw [hmark 1 x hx]
    exact mem_image_of_mem (B 1) (sphere_subset_closedBall (g 1 x).property)
  obtain ⟨K₀, hK₀, hK₀O, hK₀arc, Φ₀, hΦ₀zero, hΦ₀s, hΦ₀i, hΦ₀fix, hΦ₀match⟩ :=
    exists_supported_disk_isotopy_of_common_arc (A 0) (B 0) hr (f 0) (g 0)
      (hfi 0) (hfl 0) (hgi 0) (hgl 0) (hmark 0) (V 0) (hV 0) (hmarkV 0)
      (hside 0) (Pᶜ ∩ Lᶜ) (hP.isOpen_compl.inter hL.isClosed.isOpen_compl)
      (fun x hx => ⟨fun hxp => hx.2 (hAP 0 ⟨hx.1, hxp⟩),
        fun hxl => disjoint_left.mp hA hx.1 (hLA hxl)⟩)
      (fun x hx => ⟨fun hxp => hx.2 (hBP 0 ⟨hx.1, hxp⟩),
        fun hxl => disjoint_left.mp hB hx.1 (hLB hxl)⟩)
  have hK₀P : Disjoint K₀ P := disjoint_left.mpr (fun x hx => (hK₀O hx).1)
  have hK₀L : K₀ ⊆ Lᶜ := fun x hx => (hK₀O hx).2
  let Q := Φ₀ 1
  let A' := (A 1).trans Q
  have hQfix (x : E2) (hx : x ∉ K₀) : Q x = x := hΦ₀fix 1 x hx
  have hQP (x : E2) (hx : x ∈ P) : Q x = x :=
    hQfix x (fun h => disjoint_left.mp hK₀P h hx)
  have hQL (x : E1) (hx : x ∈ closedBall 0 r) : Q (A 1 (f 1 x)) = A 1 (f 1 x) :=
    hQfix _ (fun h => hK₀L h (mem_image_of_mem _ hx))
  have hnewmark (x : E1) (hx : x ∈ closedBall 0 r) : A' (f 1 x) = B 1 (g 1 x) :=
    (hQL x hx).trans (hmark 1 x hx)
  have hnewV : (fun x => A' (f 1 x)) '' closedBall (0 : E1) r ⊆ V 1 ∩ K₀ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    change Q (A 1 (f 1 x)) ∈ _
    rw [hQL x hx]
    exact ⟨hmarkV 1 (mem_image_of_mem _ hx), fun h => hK₀L h (mem_image_of_mem _ hx)⟩
  have hnewside : (V 1 ∩ K₀ᶜ) ∩ (A' '' closedBall 0 1) =
      (V 1 ∩ K₀ᶜ) ∩ (B 1 '' closedBall 0 1) := by
    ext x
    constructor
    · rintro ⟨hx, y, hy, he⟩
      have hey : A 1 y = x := Q.injective (he.trans (hQfix x hx.2).symm)
      have ha : x ∈ A 1 '' closedBall 0 1 := ⟨y, hy, hey⟩
      exact ⟨hx, (show x ∈ V 1 ∩ (B 1 '' closedBall 0 1) from
        hside 1 ▸ ⟨hx.1, ha⟩).2⟩
    · rintro ⟨hx, hxb⟩
      obtain ⟨y, hy, he⟩ := (show x ∈ V 1 ∩ (A 1 '' closedBall 0 1) from
        (hside 1).symm ▸ ⟨hx.1, hxb⟩).2
      refine ⟨hx, y, hy, ?_⟩
      change Q (A 1 y) = x
      rw [he, hQfix x hx.2]
  have hnewdis : Disjoint (A' '' closedBall 0 1) (B 0 '' closedBall 0 1) := by
    apply disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ hx
    obtain ⟨z, hz, he⟩ := hΦ₀match.symm ▸ hx
    have he' : z = A 1 y := Q.injective he
    exact disjoint_left.mp hA hz (he'.symm ▸ mem_image_of_mem (A 1) hy)
  have hnewarc : (fun x => A' (f 1 x)) '' closedBall (0 : E1) 1 =
      (fun x => A 1 (f 1 x)) '' closedBall (0 : E1) 1 :=
    image_congr (fun x hx => hQL x (closedBall_subset_closedBall hr.le hx))
  have hnewAP : (A' '' closedBall 0 1) ∩ P ⊆
      (fun x => A' (f 1 x)) '' closedBall (0 : E1) 1 := by
    rintro x ⟨⟨y, hy, he⟩, hxP⟩
    have hey : A 1 y = x := Q.injective (he.trans (hQP x hxP).symm)
    rw [hnewarc]
    exact hAP 1 ⟨⟨y, hy, hey⟩, hxP⟩
  have hB₀closed : IsClosed (B 0 '' closedBall (0 : E2) 1) :=
    ((isCompact_closedBall _ _).image (B 0).continuous).isClosed
  obtain ⟨K₁, hK₁, hK₁O, hK₁arc, Φ₁, hΦ₁zero, hΦ₁s, hΦ₁i, hΦ₁fix, hΦ₁match⟩ :=
    exists_supported_disk_isotopy_of_common_arc A' (B 1) hr (f 1) (g 1)
      (hfi 1) (hfl 1) (hgi 1) (hgl 1) hnewmark (V 1 ∩ K₀ᶜ)
      ((hV 1).inter hK₀.isClosed.isOpen_compl) hnewV hnewside
      (Pᶜ ∩ (B 0 '' closedBall 0 1)ᶜ) (hP.isOpen_compl.inter hB₀closed.isOpen_compl)
      (fun x hx => ⟨fun hxp => hx.2 (hnewAP ⟨hx.1, hxp⟩),
        fun hxB => disjoint_left.mp hnewdis hx.1 hxB⟩)
      (fun x hx => ⟨fun hxp => hx.2 (hnewarc.symm ▸ hBP 1 ⟨hx.1, hxp⟩),
        fun hxB => disjoint_left.mp hB hxB hx.1⟩)
  have hK₁P : Disjoint K₁ P := disjoint_left.mpr (fun x hx => (hK₁O hx).1)
  have hK₁B : K₁ ⊆ (B 0 '' closedBall 0 1)ᶜ := fun x hx => (hK₁O hx).2
  rw [hnewarc] at hK₁arc
  let Φ (t : Real) := (Φ₀ t).trans (Φ₁ t)
  have hcompact : IsCompact (K₀ ∪ K₁) := hK₀.union hK₁
  have hKP : Disjoint (K₀ ∪ K₁) P := disjoint_union_left.mpr ⟨hK₀P, hK₁P⟩
  have hfix (t : Real) (x : E2) (hx : x ∉ K₀ ∪ K₁) : Φ t x = x := by
    change Φ₁ t (Φ₀ t x) = x
    rw [hΦ₀fix t x (fun h => hx (Or.inl h)), hΦ₁fix t x (fun h => hx (Or.inr h))]
  refine ⟨K₀ ∪ K₁, hcompact, hKP, ?_, Φ, ?_, ?_, ?_, hfix, ?_, ?_⟩
  · intro i
    apply disjoint_union_left.mpr
    fin_cases i
    · refine ⟨hK₀arc, disjoint_left.mpr ?_⟩
      rintro x hx ⟨y, hy, rfl⟩
      apply hK₁B hx
      change A 0 (f 0 y) ∈ B 0 '' closedBall 0 1
      rw [hmark 0 y (closedBall_subset_closedBall hr.le hy)]
      exact mem_image_of_mem (B 0) (sphere_subset_closedBall (g 0 y).property)
    · refine ⟨disjoint_left.mpr ?_, hK₁arc⟩
      intro x hx hxm
      exact hK₀L hx (image_mono (closedBall_subset_closedBall hr.le) hxm)
  · intro x
    change Φ₁ 0 (Φ₀ 0 x) = x
    rw [hΦ₀zero, hΦ₁zero]
  · exact hΦ₁s.comp (contDiff_fst.prodMk hΦ₀s)
  · exact hΦ₀i.comp (contDiff_fst.prodMk hΦ₁i)
  · intro i
    change (Φ₁ 1 ∘ Φ₀ 1) '' (A i '' closedBall 0 1) = _
    rw [image_comp]
    fin_cases i
    · change Φ₁ 1 '' (Φ₀ 1 '' (A 0 '' closedBall 0 1)) = B 0 '' closedBall 0 1
      rw [hΦ₀match]
      exact (image_congr (fun x hx => hΦ₁fix 1 x (fun h => hK₁B h hx))).trans
        (image_id _)
    · change Φ₁ 1 '' (Φ₀ 1 '' (A 1 '' closedBall 0 1)) = B 1 '' closedBall 0 1
      simpa only [A', Q, Diffeomorph.coe_trans, image_comp] using hΦ₁match

  · exact ⟨(K₀ ∪ K₁)ᶜ, hcompact.isClosed.isOpen_compl,
      fun x hxP hxK => disjoint_left.mp hKP hxK hxP, fun t x hx => hfix t x hx⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
