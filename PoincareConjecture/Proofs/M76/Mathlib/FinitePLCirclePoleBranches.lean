import PoincareConjecture.Proofs.M76.Mathlib.ClosedRegionPatchIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.not_both_subset_of_endpoint_contact
    {U s t : Set E} {a b : E} (hU : IsFinitePLBallPair ℝ U {a, b})
    (hab : a ≠ b) (hs : IsPreconnected s) (ht : IsPreconnected t)
    (has : a ∈ s) (hat : a ∈ t)
    (hneS : ∃ x ∈ s, x ≠ a) (hneT : ∃ x ∈ t, x ≠ a)
    (hst : s ∩ t ⊆ {a}) : ¬ (s ⊆ U ∧ t ⊆ U) := by
  rintro ⟨hsU, htU⟩
  obtain ⟨e, _, hea, _⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  let f : U → ℝ := fun x => (e.symm x : ℝ)
  have hf : Continuous f := continuous_subtype_val.comp e.symm.continuous
  have hzero (x : U) : f x = 0 ↔ (x : E) = a := by
    constructor
    · intro hx
      have hx0 : e.symm x = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := Subtype.ext hx
      have heq := congrArg (fun y : Icc (0 : ℝ) 1 => (e y : E)) hx0
      rw [e.apply_symm_apply] at heq
      exact heq.trans hea
    · intro hx
      have hxe : x = e ⟨0, ⟨le_rfl, zero_le_one⟩⟩ :=
        Subtype.ext (hx.trans hea.symm)
      simp only [f, hxe, e.symm_apply_apply]
  let fs : s → ℝ := fun x => f ⟨x, hsU x.property⟩
  let ft : t → ℝ := fun x => f ⟨x, htU x.property⟩
  have hfs : Continuous fs :=
    hf.comp (continuous_subtype_val.subtype_mk fun x => hsU x.property)
  have hft : Continuous ft :=
    hf.comp (continuous_subtype_val.subtype_mk fun x => htU x.property)
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  let : PreconnectedSpace t := isPreconnected_iff_preconnectedSpace.mp ht
  have hs0 : (0 : ℝ) ∈ range fs :=
    ⟨⟨a, has⟩, (hzero ⟨a, hsU has⟩).mpr rfl⟩
  have ht0 : (0 : ℝ) ∈ range ft :=
    ⟨⟨a, hat⟩, (hzero ⟨a, htU hat⟩).mpr rfl⟩
  obtain ⟨x, hxs, hxa⟩ := hneS
  obtain ⟨y, hyt, hya⟩ := hneT
  have hfx : 0 < fs ⟨x, hxs⟩ := lt_of_le_of_ne
    (e.symm ⟨x, hsU hxs⟩).property.1
    (fun heq => hxa ((hzero ⟨x, hsU hxs⟩).mp heq.symm))
  have hfy : 0 < ft ⟨y, hyt⟩ := lt_of_le_of_ne
    (e.symm ⟨y, htU hyt⟩).property.1
    (fun heq => hya ((hzero ⟨y, htU hyt⟩).mp heq.symm))
  let r : ℝ := min (fs ⟨x, hxs⟩) (ft ⟨y, hyt⟩) / 2
  have hr : 0 < r := half_pos (lt_min hfx hfy)
  have hrf : r ≤ fs ⟨x, hxs⟩ := by
    have := min_le_left (fs ⟨x, hxs⟩) (ft ⟨y, hyt⟩)
    dsimp only [r]
    linarith
  have hrg : r ≤ ft ⟨y, hyt⟩ := by
    have := min_le_right (fs ⟨x, hxs⟩) (ft ⟨y, hyt⟩)
    dsimp only [r]
    linarith
  obtain ⟨v, hv⟩ := (isPreconnected_range hfs).Icc_subset hs0
    (mem_range_self ⟨x, hxs⟩) ⟨hr.le, hrf⟩
  obtain ⟨w, hw⟩ := (isPreconnected_range hft).Icc_subset ht0
    (mem_range_self ⟨y, hyt⟩) ⟨hr.le, hrg⟩
  have hcoords : e.symm ⟨v, hsU v.property⟩ = e.symm ⟨w, htU w.property⟩ :=
    Subtype.ext (hv.trans hw.symm)
  have hvw : (v : E) = w := congrArg Subtype.val (e.symm.injective hcoords)
  have hva : (v : E) = a := hst ⟨v.property, hvw.symm ▸ w.property⟩
  have hv0 : fs v = 0 := (hzero ⟨v, hsU v.property⟩).mpr hva
  exact hr.ne' (hv.symm.trans hv0)

theorem exists_opposite_circle_arc_labels
    (arc d : Bool → Set E) {a b : E} (c : Bool → E)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i) {a, b})
    (hab : a ≠ b) (hArcInter : Pairwise (fun i j => arc i ∩ arc j = {a, b}))
    (hd : ∀ i, IsFinitePLBallPair ℝ (d i) {a, c i})
    (hc : ∀ i, c i ≠ a) (hcover : ∀ i, d i ⊆ ⋃ j, arc j)
    (hmiss : ∀ i, b ∉ d i) (hinter : d false ∩ d true = {a}) :
    ∃ i : Bool, d false ⊆ arc i ∧ d true ⊆ arc (!i) := by
  have hchoose (j : Bool) : ∃ i, d j ⊆ arc i := by
    have havoid : Disjoint (d j \ {a, c j}) ({a, b} : Set E) := by
      apply disjoint_left.mpr
      intro x hx hxm
      rcases hxm with hxa | hxb
      · exact hx.2 (Or.inl hxa)
      · exact hmiss j (hxb ▸ hx.1)
    obtain ⟨i, hi⟩ := (hd j).isConnected_sdiff.exists_closure_subset_of_finite_closed_cover
      arc (fun i => (hArc i).isCompact.isClosed) (sdiff_subset.trans (hcover j))
      (fun i k hik => (hArcInter hik).subset) havoid
    exact ⟨i, by rwa [(hd j).closure_sdiff] at hi⟩
  obtain ⟨i, hi⟩ := hchoose false
  obtain ⟨j, hj⟩ := hchoose true
  have hij : i ≠ j := by
    intro heq
    subst j
    exact (hArc i).not_both_subset_of_endpoint_contact hab
      (hd false).isConnected.isPreconnected (hd true).isConnected.isPreconnected
      ((hd false).1 (Or.inl rfl)) ((hd true).1 (Or.inl rfl))
      ⟨c false, (hd false).1 (Or.inr rfl), hc false⟩
      ⟨c true, (hd true).1 (Or.inr rfl), hc true⟩ hinter.subset ⟨hi, hj⟩
  have hjnot : j = !i := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · rfl
    · rfl
    · exact (hij rfl).elim
  exact ⟨i, hi, hjnot ▸ hj⟩

end Set
