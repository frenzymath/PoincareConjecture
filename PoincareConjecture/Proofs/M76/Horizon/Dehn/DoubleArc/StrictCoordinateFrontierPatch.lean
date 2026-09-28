import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

def strictCoordinateWedge (signs : Fin 2 → Bool) : Set V3 :=
  {x | ∀ i : Fin 2, if signs i then 0 < x i.castSucc else x i.castSucc < 0}

theorem strictCoordinateWedge_convex (signs : Fin 2 → Bool) :
    Convex ℝ (strictCoordinateWedge signs) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  change if signs i then 0 < a * x i.castSucc + b * y i.castSucc
    else a * x i.castSucc + b * y i.castSucc < 0
  cases hsi : signs i <;> simp only [hsi, Bool.false_eq_true, ↓reduceIte] at hxi hyi ⊢
  · have hax := mul_nonpos_of_nonneg_of_nonpos ha hxi.le
    have hby := mul_nonpos_of_nonneg_of_nonpos hb hyi.le
    rcases eq_or_lt_of_le ha with h | h
    · subst a
      have : b = 1 := by linarith
      simpa only [this, zero_mul, one_mul, zero_add] using hyi
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg h hxi) hby
  · have hax := mul_nonneg ha hxi.le
    have hby := mul_nonneg hb hyi.le
    rcases eq_or_lt_of_le ha with h | h
    · subst a
      have : b = 1 := by linarith
      simpa only [this, zero_mul, one_mul, zero_add] using hyi
    · exact add_pos_of_pos_of_nonneg (mul_pos h hxi) hby

theorem strictCoordinateWedge_nonempty (signs : Fin 2 → Bool) :
    (strictCoordinateWedge signs).Nonempty := by
  refine ⟨![if signs 0 then 1 else -1, if signs 1 then 1 else -1, 0], ?_⟩
  intro i
  fin_cases i
  · change if signs 0 then 0 < (if signs 0 then (1 : ℝ) else -1)
      else (if signs 0 then (1 : ℝ) else -1) < 0
    cases signs 0 <;> norm_num
  · change if signs 1 then 0 < (if signs 1 then (1 : ℝ) else -1)
      else (if signs 1 then (1 : ℝ) else -1) < 0
    cases signs 1 <;> norm_num

theorem strictCoordinateWedge_ne_zero {signs : Fin 2 → Bool}
    {x : V3} (hx : x ∈ strictCoordinateWedge signs) : x ≠ 0 := by
  intro h
  have hx0 := hx 0
  subst x
  cases signs 0 <;> simp at hx0

theorem strictCoordinateWedge_smul {signs : Fin 2 → Bool}
    {x : V3} (hx : x ∈ strictCoordinateWedge signs) {r : ℝ} (hr : 0 < r) :
    r • x ∈ strictCoordinateWedge signs := by
  intro i
  have hxi := hx i
  change if signs i then 0 < r * x i.castSucc else r * x i.castSucc < 0
  cases hsi : signs i <;> simp only [hsi, Bool.false_eq_true, ↓reduceIte] at hxi ⊢
  · exact mul_neg_of_pos_of_neg hr hxi
  · exact mul_pos hr hxi

theorem isConnected_strictCoordinate_frontier_patch {C : Set V3}
    (hC : IsCompact C) (hcv : Convex ℝ C) (hzero : (0 : V3) ∈ interior C)
    (signs : Fin 2 → Bool) :
    IsConnected (frontier C ∩ strictCoordinateWedge signs) := by
  let r : V3 → V3 := fun x => (gauge C x)⁻¹ • x
  have hrad (x : V3) (hx : x ∈ strictCoordinateWedge signs) :
      0 < (gauge C x)⁻¹ ∧ r x ∈ frontier C :=
    hC.gauge_inv_smul_mem_frontier hcv hzero (strictCoordinateWedge_ne_zero hx)
  have hr : ContinuousOn r (strictCoordinateWedge signs) := by
    have hginv : ContinuousOn (fun x => (gauge C x)⁻¹) (strictCoordinateWedge signs) := by
      apply (continuous_gauge hcv (mem_interior_iff_mem_nhds.mp hzero)).continuousOn.inv₀
      intro x hx h
      exact (hrad x hx).1.ne' (by simp only [h, inv_zero])
    exact hginv.smul continuous_id.continuousOn
  have himage : r '' strictCoordinateWedge signs =
      frontier C ∩ strictCoordinateWedge signs := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hrad x hx).2, strictCoordinateWedge_smul hx (hrad x hx).1⟩
    · rintro ⟨hy, hys⟩
      refine ⟨y, hys, ?_⟩
      have hg := (gauge_eq_one_iff_mem_frontier hcv
        (mem_interior_iff_mem_nhds.mp hzero)).mpr hy
      simp only [r, hg, inv_one, one_smul]
  rw [← himage]
  exact ((strictCoordinateWedge_convex signs).isConnected
    (strictCoordinateWedge_nonempty signs)).image r hr

theorem exists_strict_frontier_point_outside_two_closed_sets
    {C J₀ J₁ : Set V3} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : V3) ∈ interior C) (signs : Fin 2 → Bool)
    (hJ₀ : IsClosed J₀) (hJ₁ : IsClosed J₁) (hdisj : Disjoint J₀ J₁)
    (hmeet₀ : (frontier C ∩ strictCoordinateWedge signs ∩ J₀).Nonempty)
    (hmeet₁ : (frontier C ∩ strictCoordinateWedge signs ∩ J₁).Nonempty) :
    ∃ y ∈ frontier C, y ∈ strictCoordinateWedge signs ∧ y ∉ J₀ ∧ y ∉ J₁ := by
  by_contra h
  have hcover : frontier C ∩ strictCoordinateWedge signs ⊆ J₀ ∪ J₁ := by
    intro y hy
    by_contra hn
    exact h ⟨y, hy.1, hy.2, fun h₀ => hn (Or.inl h₀), fun h₁ => hn (Or.inr h₁)⟩
  obtain ⟨y, hy, hy₀, hy₁⟩ := isPreconnected_closed_iff.mp
    (isConnected_strictCoordinate_frontier_patch hC hcv hzero signs).isPreconnected
    J₀ J₁ hJ₀ hJ₁ hcover hmeet₀ hmeet₁
  exact Set.disjoint_left.mp hdisj hy₀ hy₁

theorem exists_strict_chart_frontier_point_outside_two_compact_sets
    {E : Type*} [NormedAddCommGroup E] {V : Set E} {C : Set V3}
    (theta : V ≃ₜ C) (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : V3) ∈ interior C) (J : Bool → Set E)
    (hJ : ∀ j, IsCompact (J j)) (hJV : ∀ j, J j ⊆ V)
    (hdisj : Disjoint (J false) (J true)) (signs : Fin 2 → Bool)
    (hmeet : ∀ j, ∃ z : V, (z : E) ∈ J j ∧
      (theta z : V3) ∈ frontier C ∧ (theta z : V3) ∈ strictCoordinateWedge signs) :
    ∃ z : V, (theta z : V3) ∈ frontier C ∧
      (theta z : V3) ∈ strictCoordinateWedge signs ∧ ∀ j, (z : E) ∉ J j := by
  let f (j : Bool) : J j → V3 := fun x => theta ⟨x, hJV j x.property⟩
  have hf (j : Bool) : Continuous (f j) :=
    continuous_subtype_val.comp (theta.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hc (j : Bool) : IsCompact (range (f j)) := by
    letI : CompactSpace (J j) := isCompact_iff_compactSpace.mp (hJ j)
    exact isCompact_range (hf j)
  have hd : Disjoint (range (f false)) (range (f true)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨a, ha⟩ ⟨b, hb⟩
    have he : (a : E) = b := congrArg Subtype.val
      (theta.injective (Subtype.ext (ha.trans hb.symm)))
    exact Set.disjoint_left.mp hdisj a.property (he ▸ b.property)
  have hm (j : Bool) : (frontier C ∩ strictCoordinateWedge signs ∩ range (f j)).Nonempty := by
    obtain ⟨z, hz, hfront, hstrict⟩ := hmeet j
    exact ⟨theta z, ⟨hfront, hstrict⟩, ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨y, hy, hs, hn₀, hn₁⟩ := exists_strict_frontier_point_outside_two_closed_sets
    hC hcv hzero signs (hc false).isClosed (hc true).isClosed hd (hm false) (hm true)
  have hyC : y ∈ C := hC.isClosed.closure_eq ▸ frontier_subset_closure hy
  let z : V := theta.symm ⟨y, hyC⟩
  have htheta : (theta z : V3) = y := by simp only [z, Homeomorph.apply_symm_apply]
  refine ⟨z, htheta.symm ▸ hy, htheta.symm ▸ hs, ?_⟩
  intro j hz
  have hfmem : y ∈ range (f j) := ⟨⟨z, hz⟩, htheta⟩
  cases j
  · exact hn₀ hfmem
  · exact hn₁ hfmem

end PoincareConjecture.M76.Dehn
