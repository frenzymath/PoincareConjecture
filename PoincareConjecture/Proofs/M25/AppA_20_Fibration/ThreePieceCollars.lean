import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M25.Mathlib.ProductBoundaryTransition
import Mathlib.Geometry.Manifold.Instances.Sphere











set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25




theorem exists_signed_collars_of_three_product_charts
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {eta : ℝ} (heta : 0 < eta)
    (e : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : ∀ i : Fin 3,
      (e i).source = univ ×ˢ Ioo (-eta) (1 + eta))
    (hsmooth : ∀ i : Fin 3,
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i) (e i).source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm (e i).target)
    (hboundary : ∀ i : Fin 3,
      range (fun q : UnitTwoSphere => e i (q, 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hinter : ∀ i : Fin 3,
      (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hcover : (⋃ i : Fin 3, e i '' (univ ×ˢ Icc (0 : ℝ) 1)) = univ) :
    let K : Fin 3 → Set M := fun i => e i '' (univ ×ˢ Icc (0 : ℝ) 1)
    ∃ delta : ℝ, 0 < delta ∧ delta < eta ∧ delta < 1 / 8 ∧
      (∀ (i : Fin 3) (q : UnitTwoSphere) (s : ℝ),
        s ∈ Ioo (-delta) delta →
          e i (q, s) ∈ (e (i - 1)).target ∧
          (e i (q, s) ∈ K i ↔ 0 ≤ s) ∧
          (e i (q, s) ∈ K (i - 1) ↔ s ≤ 0) ∧
          e i (q, s) ∉ K (i + 1)) ∧
      (∀ (i : Fin 3) (q : UnitTwoSphere) (s : ℝ),
        s ∈ Ioo (1 - delta) (1 + delta) →
          e i (q, s) ∈ (e (i + 1)).target ∧
          0 < deriv (fun t : ℝ => ((e (i + 1)).symm (e i (q, t))).2) s) := by
  classical
  dsimp only
  let C : Set RoundCylinderSpace := univ ×ˢ Icc (0 : ℝ) 1
  let K : Fin 3 → Set M := fun i => e i '' C
  have hC (i : Fin 3) : C ⊆ (e i).source := by
    intro z hz
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hC0 (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ C := by simp [C]
  have hC1 (q : UnitTwoSphere) : (q, (1 : ℝ)) ∈ C := by simp [C]
  have hcompact : IsCompact C := isCompact_univ.prod isCompact_Icc
  have hclosed (i : Fin 3) : IsClosed (K i) :=
    (hcompact.image_of_continuousOn ((e i).continuousOn.mono (hC i))).isClosed
  have hprev (i : Fin 3) (q : UnitTwoSphere) : e i (q, 0) ∈ K (i - 1) := by
    have hb := hboundary (i - 1)
    rw [sub_add_cancel] at hb
    have hx : e i (q, 0) ∈ range (fun p : UnitTwoSphere => e (i - 1) (p, 1)) := by
      rw [hb]
      exact ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hx
    exact ⟨(p, 1), hC1 p, hp⟩
  have hprevTarget (i : Fin 3) (q : UnitTwoSphere) :
      e i (q, 0) ∈ (e (i - 1)).target := by
    obtain ⟨z, hz, hzx⟩ := hprev i q
    exact hzx ▸ (e (i - 1)).map_source (hC (i - 1) hz)
  have havoid (i : Fin 3) (q : UnitTwoSphere) : e i (q, 0) ∉ K (i + 1) := by
    intro hx
    have hboth : e i (q, 0) ∈ K i ∩ K (i + 1) :=
      ⟨⟨(q, 0), hC0 q, rfl⟩, hx⟩
    change e i (q, 0) ∈
      (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
        (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) at hboth
    rw [hinter i, ← hboundary i] at hboth
    obtain ⟨p, hp⟩ := hboth
    have hpq := (e i).injOn (hC i (hC1 p)) (hC i (hC0 q)) hp
    have hbad : (1 : ℝ) = 0 := congrArg Prod.snd hpq
    norm_num at hbad
  let O : Fin 3 → Set RoundCylinderSpace := fun i =>
    (e i).source ∩ (e i) ⁻¹' ((e (i - 1)).target ∩ (K (i + 1))ᶜ)
  have hopen (i : Fin 3) : IsOpen (O i) :=
    (e i).continuousOn.isOpen_inter_preimage (e i).open_source
      ((e (i - 1)).open_target.inter (hclosed (i + 1)).isOpen_compl)
  have hslice (i : Fin 3) : (univ : Set UnitTwoSphere) ×ˢ {(0 : ℝ)} ⊆ O i := by
    rintro ⟨q, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := mem_singleton_iff.mp hs
    subst s
    exact ⟨hC i (hC0 q), hprevTarget i q, havoid i q⟩
  have hlower (i : Fin 3) :
      ∃ a : ℝ, 0 < a ∧ univ ×ˢ Ioo (-a) a ⊆ O i := by
    obtain ⟨U, V, _, hV, hU, hV0, hUV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton (hopen i) (hslice i)
    have h0V : (0 : ℝ) ∈ V := hV0 (mem_singleton 0)
    obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
    refine ⟨a, ha, ?_⟩
    intro z hz
    have hzV : z.2 ∈ V := hball (by simpa [Real.dist_eq] using abs_lt.mpr hz.2)
    exact hUV ⟨hU (mem_univ z.1), hzV⟩
  choose a ha hband using hlower
  have hupper (i : Fin 3) :=
    OpenPartialHomeomorph.exists_positive_scalar_boundary_transition
      (e i) (e (i + 1)) (hC i) (hC (i + 1))
      (hsmooth i).1 (hsmooth i).2 (hsmooth (i + 1)).1 (hsmooth (i + 1)).2
      (hboundary i) (hinter i)
  choose r hr _hrquarter hrsource _hrzero hrderiv using hupper
  let m : Fin 3 → ℝ := fun i => min (a i) (r i)
  have hm (i : Fin 3) : 0 < m i := lt_min (ha i) (hr i)
  have hmin : 0 < min eta (min (1 / 8 : ℝ) (min (m 0) (min (m 1) (m 2)))) :=
    lt_min heta (lt_min (by norm_num) (lt_min (hm 0) (lt_min (hm 1) (hm 2))))
  obtain ⟨delta, hd, hsmall⟩ := exists_between hmin
  obtain ⟨hdeta, hsmall⟩ := lt_min_iff.mp hsmall
  obtain ⟨hdeighth, hsmall⟩ := lt_min_iff.mp hsmall
  obtain ⟨hd0, hsmall⟩ := lt_min_iff.mp hsmall
  obtain ⟨hd1, hd2⟩ := lt_min_iff.mp hsmall
  have hdm (i : Fin 3) : delta < m i := by
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
  have hda (i : Fin 3) : delta < a i := (hdm i).trans_le (min_le_left _ _)
  have hdr (i : Fin 3) : delta < r i := (hdm i).trans_le (min_le_right _ _)
  refine ⟨delta, hd, hdeta, hdeighth, ?_, ?_⟩
  · intro i q s hs
    have hsa : s ∈ Ioo (-(a i)) (a i) := by
      constructor <;> linarith [hs.1, hs.2, hda i]
    have hO : (q, s) ∈ O i := hband i ⟨mem_univ _, hsa⟩
    have hssource : (q, s) ∈ (e i).source := hO.1
    have hcurrent : e i (q, s) ∈ K i ↔ 0 ≤ s := by
      constructor
      · rintro ⟨z, hz, hzx⟩
        have hzs := congrArg Prod.snd ((e i).injOn (hC i hz) hssource hzx)
        change z.2 = s at hzs
        rw [← hzs]
        exact hz.2.1
      · intro hs0
        exact ⟨(q, s), ⟨mem_univ _, hs0, by linarith [hs.2]⟩, rfl⟩
    have hprevious : e i (q, s) ∈ K (i - 1) ↔ s ≤ 0 := by
      constructor
      · intro hx
        by_contra hnot
        have hspos : 0 < s := lt_of_not_ge hnot
        have hboth : e i (q, s) ∈ K (i - 1) ∩ K i :=
          ⟨hx, hcurrent.mpr hspos.le⟩
        have hi := hinter (i - 1)
        rw [sub_add_cancel] at hi
        change K (i - 1) ∩ K i = range (fun p : UnitTwoSphere => e i (p, 0)) at hi
        rw [hi] at hboth
        obtain ⟨p, hp⟩ := hboth
        have hzero : (0 : ℝ) = s :=
          congrArg Prod.snd ((e i).injOn (hC i (hC0 p)) hssource hp)
        linarith
      · intro hsnonpos
        by_cases hs0 : s = 0
        · simpa only [hs0] using hprev i q
        · have hsneg : s < 0 := lt_of_le_of_ne hsnonpos hs0
          have hnotcurrent : e i (q, s) ∉ K i := fun hx => (not_le_of_gt hsneg) (hcurrent.mp hx)
          have hwhole : e i (q, s) ∈ ⋃ j : Fin 3, K j := by
            change e i (q, s) ∈ ⋃ j : Fin 3, e j '' (univ ×ˢ Icc (0 : ℝ) 1)
            rw [hcover]
            exact mem_univ _
          obtain ⟨j, hj⟩ := mem_iUnion.mp hwhole
          have hcases : j = i ∨ j = i - 1 ∨ j = i + 1 := by
            fin_cases i <;> fin_cases j <;> decide
          rcases hcases with hji | hji | hji
          · exact False.elim (hnotcurrent (hji ▸ hj))
          · exact hji ▸ hj
          · exact False.elim (hO.2.2 (hji ▸ hj))
    exact ⟨hO.2.1, hcurrent, hprevious, hO.2.2⟩
  · intro i q s hs
    have hsr : s ∈ Ioo (1 - r i) (1 + r i) := by
      constructor <;> linarith [hs.1, hs.2, hdr i]
    have htransition : (q, s) ∈ ((e i).trans (e (i + 1)).symm).source :=
      hrsource i ⟨mem_univ _, hsr⟩
    exact ⟨htransition.2, hrderiv i q s hsr⟩

end PoincareConjecture.M25
