import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.SignedCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting

set_option autoImplicit false
open Set BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

private noncomputable def inwardHeight (s : unitInterval) (u : ℝ) : ℝ :=
  u + (s : ℝ) * max 0 (1 / 2 - |u|) / 2

private theorem inwardHeight_eq (s : unitInterval) {u : ℝ} (hu : 1 / 2 ≤ |u|) :
    inwardHeight s u = u := by
  rw [inwardHeight, max_eq_left (by linarith : 1 / 2 - |u| ≤ 0)]
  simp

private theorem inwardHeight_mem (s : unitInterval) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) : inwardHeight s u ∈ Ioo (-1 : ℝ) 1 := by
  by_cases h : 1 / 2 ≤ |u|
  · simpa only [inwardHeight_eq s h] using hu
  · have habs : |u| < 1 / 2 := lt_of_not_ge h
    have hb : 0 ≤ 1 / 2 - |u| := by linarith
    have hm := mul_nonneg s.property.1 hb
    have hm' := mul_le_mul_of_nonneg_right s.property.2 hb
    rw [inwardHeight, max_eq_right hb]
    constructor
    · linarith [hu.1]
    · linarith [le_abs_self u]

private theorem le_inwardHeight (s : unitInterval) (u : ℝ) : u ≤ inwardHeight s u := by
  have h := mul_nonneg s.property.1 (le_max_left 0 (1 / 2 - |u|))
  dsimp [inwardHeight]
  linarith

private theorem inwardHeight_one_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < inwardHeight 1 u := by
  rcases eq_or_lt_of_le hu with h | h
  · subst u
    norm_num [inwardHeight]
  · exact h.trans_le (le_inwardHeight 1 u)

theorem exists_inward_motion_of_open_bicollar
    {X : Type*} [TopologicalSpace X] [T2Space X] {S U : Set X}
    (hS : IsClosed S) (hcompact : IsCompact (frontier S)) (hU : IsOpen U)
    (H : (frontier S × Ioo (-1 : ℝ) 1) ≃ₜ U)
    (hbase : ∀ x, (H (bicollarBase x) : X) = (x : X))
    (hpos : ∀ z, (H z : X) ∈ S ↔ 0 ≤ (z.2 : ℝ))
    (hneg : ∀ z, (H z : X) ∈ (interior S)ᶜ ↔ (z.2 : ℝ) ≤ 0) :
    ∃ D : C(unitInterval × X, X),
      (∀ x, D (0, x) = x) ∧
      (∀ t, MapsTo (fun x => D (t, x)) S S) ∧
      (∀ t, MapsTo (fun x => D (t, x)) (interior S) (interior S)) ∧
      MapsTo (fun x => D (1, x)) S (interior S) := by
  classical
  let E := ↥(frontier S)
  let : CompactSpace E := isCompact_iff_compactSpace.mp hcompact
  let J := Icc (-(1 / 2) : ℝ) (1 / 2)
  let f : E × J → X := fun z => H (z.1, ⟨z.2, by
    constructor <;> linarith [z.2.property.1, z.2.property.2]⟩)
  have hf : Continuous f := continuous_subtype_val.comp (H.continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))
  let A : Set X := range f
  have hAc : IsCompact A := isCompact_range hf
  have hAU : A ⊆ U := by
    rintro x ⟨z, rfl⟩
    exact (H _).property
  let k : A → E × Ioo (-1 : ℝ) 1 := fun x => H.symm ⟨x, hAU x.property⟩
  have hk : Continuous k := H.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hkval (x : A) : (H (k x) : X) = x := by
    exact congrArg Subtype.val (H.apply_symm_apply ⟨x, hAU x.property⟩)
  have hint (z : E × Ioo (-1 : ℝ) 1) :
      (H z : X) ∈ interior S ↔ 0 < (z.2 : ℝ) := by
    have h := not_congr (hneg z)
    simpa only [mem_compl_iff, not_not, not_le] using h
  let q : unitInterval × A → E × Ioo (-1 : ℝ) 1 := fun z =>
    ((k z.2).1, ⟨inwardHeight z.1 (k z.2).2, inwardHeight_mem z.1 (k z.2).2.property⟩)
  have hq : Continuous q := by
    have hs : Continuous (fun z : unitInterval × A => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hu : Continuous (fun z : unitInterval × A => ((k z.2).2 : ℝ)) :=
      continuous_subtype_val.comp (hk.comp continuous_snd).snd
    exact ((hk.comp continuous_snd).fst.prodMk
      ((hu.add ((hs.mul (continuous_const.max (continuous_const.sub hu.abs))).div_const 2)).subtype_mk _))
  let G : C(unitInterval × A, X) :=
    ⟨fun z => H (q z), continuous_subtype_val.comp (H.continuous.comp hq)⟩
  let P : C(unitInterval × X, X) := ⟨Prod.snd, continuous_snd⟩
  have hfront (s : unitInterval) (x : A) (hx : (x : X) ∈ frontier A) :
      G (s, x) = P (s, x) := by
    have habs : 1 / 2 ≤ |((k x).2 : ℝ)| := by
      by_contra h
      have hlt := lt_of_not_ge h
      let V : Set (E × Ioo (-1 : ℝ) 1) := {z | |(z.2 : ℝ)| < 1 / 2}
      have hV : IsOpen V := isOpen_lt
        (continuous_subtype_val.comp continuous_snd).abs continuous_const
      let g : E × Ioo (-1 : ℝ) 1 → X := fun z => H z
      have hg : Topology.IsOpenEmbedding g :=
        hU.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
      have hVA : g '' V ⊆ A := by
        rintro y ⟨z, hz, rfl⟩
        have hz' := abs_lt.mp (show |(z.2 : ℝ)| < 1 / 2 from hz)
        refine ⟨(z.1, ⟨z.2, ⟨hz'.1.le, hz'.2.le⟩⟩), ?_⟩
        rfl
      have hxV : (x : X) ∈ g '' V := ⟨k x, hlt, hkval x⟩
      exact hx.2 ((hg.isOpenMap V hV).subset_interior_iff.mpr hVA hxV)
    change (H ((k x).1, ⟨inwardHeight s (k x).2, _⟩) : X) = x
    trans (H (k x) : X)
    · apply congrArg (fun z => (H z : X))
      exact Prod.ext rfl (Subtype.ext (inwardHeight_eq s habs))
    · exact hkval x
  obtain ⟨D, hinner, houter⟩ :=
    ContinuousMap.exists_paste_of_eq_on_frontier hAc.isClosed G P hfront
  have hzero (x : X) : D (0, x) = x := by
    by_cases hx : x ∈ A
    · rw [hinner 0 ⟨x, hx⟩]
      change (H ((k ⟨x, hx⟩).1, ⟨inwardHeight 0 (k ⟨x, hx⟩).2, _⟩) : X) = x
      trans (H (k ⟨x, hx⟩) : X)
      · apply congrArg (fun z => (H z : X))
        exact Prod.ext rfl (Subtype.ext (by simp [inwardHeight]))
      · exact hkval ⟨x, hx⟩
    · exact houter 0 x (fun h => hx (interior_subset h))
  have hpres (s : unitInterval) : MapsTo (fun x => D (s, x)) S S := by
    intro x hxS
    change D (s, x) ∈ S
    by_cases hx : x ∈ A
    · rw [hinner s ⟨x, hx⟩]
      apply (hpos (q (s, ⟨x, hx⟩))).mpr
      have hu : 0 ≤ ((k ⟨x, hx⟩).2 : ℝ) :=
        (hpos (k ⟨x, hx⟩)).mp ((hkval ⟨x, hx⟩).symm ▸ hxS)
      exact hu.trans (le_inwardHeight s _)
    · rw [houter s x (fun h => hx (interior_subset h))]
      exact hxS
  have hpresint (s : unitInterval) :
      MapsTo (fun x => D (s, x)) (interior S) (interior S) := by
    intro x hxS
    change D (s, x) ∈ interior S
    by_cases hx : x ∈ A
    · rw [hinner s ⟨x, hx⟩]
      apply (hint (q (s, ⟨x, hx⟩))).mpr
      have hu : 0 < ((k ⟨x, hx⟩).2 : ℝ) :=
        (hint (k ⟨x, hx⟩)).mp ((hkval ⟨x, hx⟩).symm ▸ hxS)
      exact hu.trans_le (le_inwardHeight s _)
    · rw [houter s x (fun h => hx (interior_subset h))]
      exact hxS
  refine ⟨D, hzero, hpres, hpresint, ?_⟩
  intro x hxS
  change D (1, x) ∈ interior S
  by_cases hx : x ∈ A
  · rw [hinner 1 ⟨x, hx⟩]
    apply (hint (q (1, ⟨x, hx⟩))).mpr
    apply inwardHeight_one_pos
    exact (hpos (k ⟨x, hx⟩)).mp ((hkval ⟨x, hx⟩).symm ▸ hxS)
  · rw [houter 1 x (fun h => hx (interior_subset h))]
    change x ∈ interior S
    by_contra hxint
    have hxF : x ∈ frontier S := by
      rw [frontier, hS.closure_eq]
      exact ⟨hxS, hxint⟩
    apply hx
    refine ⟨(⟨x, hxF⟩, ⟨0, by constructor <;> norm_num [J]⟩), ?_⟩
    exact hbase ⟨x, hxF⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
