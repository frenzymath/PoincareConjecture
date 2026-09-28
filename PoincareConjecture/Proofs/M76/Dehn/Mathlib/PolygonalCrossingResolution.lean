import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

def source : Set P2 := Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1

def tube : Set C3 := (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1

def crossing : Set C3 := {z | z ∈ tube ∧ (z.1.2 = z.1.1 ∨ z.1.2 = -z.1.1)}

def outer (r : ℝ) : Set C3 := {z | r ≤ max |z.1.1| |z.1.2|}

noncomputable def height (b u : ℝ) : ℝ := max |u| b

noncomputable def signedHeight (b : ℝ) (positive : Bool) (u : ℝ) : ℝ :=
  if positive then height b u else -height b u

noncomputable def strip (b : ℝ) (positive : Bool) (p : P2) : C3 :=
  ((p.2, signedHeight b positive p.2), p.1)

noncomputable def alternate (b : ℝ) (positive : Bool) (p : P2) : C3 :=
  ((signedHeight b positive p.2, p.2), p.1)

def horizontalReflection (z : C3) : C3 := ((z.1.1, -z.1.2), z.2)

def verticalReflection (z : C3) : C3 := ((-z.1.1, z.1.2), z.2)

def swapTransverse (z : C3) : C3 := ((z.1.2, z.1.1), z.2)

def resolved (b : ℝ) : Set C3 := strip b true '' source ∪ strip b false '' source

def alternateResolved (b : ℝ) : Set C3 :=
  alternate b true '' source ∪ alternate b false '' source

private theorem height_nonneg (b u : ℝ) : 0 ≤ height b u :=
  (abs_nonneg u).trans (le_max_left _ _)

private theorem abs_signedHeight (b : ℝ) (positive : Bool) (u : ℝ) :
    |signedHeight b positive u| = height b u := by
  cases positive <;> simp [signedHeight, abs_of_nonneg (height_nonneg b u)]

private theorem height_eq_one_iff {b u : ℝ} (hb : b < 1) (hu : |u| ≤ 1) :
    height b u = 1 ↔ |u| = 1 := by
  constructor
  · intro h
    by_contra hn
    have hlt : height b u < 1 := max_lt (lt_of_le_of_ne hu hn) hb
    exact (ne_of_lt hlt) h
  · intro h
    change max |u| b = 1
    rw [h, max_eq_left hb.le]

theorem continuous_maps (b : ℝ) (positive : Bool) :
    Continuous (strip b positive) ∧ Continuous (alternate b positive) := by
  constructor
  · cases positive with
    | false =>
      change Continuous (fun p : P2 => ((p.2, -max |p.2| b), p.1))
      fun_prop
    | true =>
      change Continuous (fun p : P2 => ((p.2, max |p.2| b), p.1))
      fun_prop
  · cases positive with
    | false =>
      change Continuous (fun p : P2 => ((-max |p.2| b, p.2), p.1))
      fun_prop
    | true =>
      change Continuous (fun p : P2 => ((max |p.2| b, p.2), p.1))
      fun_prop

theorem embedding_maps (b : ℝ) (positive : Bool) :
    IsEmbedding (strip b positive) ∧ IsEmbedding (alternate b positive) := by
  have hs : Function.LeftInverse (fun z : C3 => (z.2, z.1.1)) (strip b positive) :=
    fun _ => rfl
  have ha : Function.LeftInverse (fun z : C3 => (z.2, z.1.2)) (alternate b positive) :=
    fun _ => rfl
  exact ⟨hs.isEmbedding (by fun_prop) (continuous_maps b positive).1,
    ha.isEmbedding (by fun_prop) (continuous_maps b positive).2⟩

theorem finitePiecewiseAffineOn_maps (b : ℝ) (positive : Bool) :
    FinitePiecewiseAffineOn (strip b positive) source ∧
      FinitePiecewiseAffineOn (alternate b positive) source := by
  have hrect := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, e, he, _⟩ := hrect
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := he
  have ht := (K.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hu := (K.affineOnFaces_affine
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hn := (K.affineOnFaces_affine
    (-ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have habs : FinitePiecewiseAffineOn (fun p : P2 => |p.2|) K.space := by
    apply (hu.max hn).congr
    intro p _
    exact (abs_eq_max_neg (a := p.2)).symm
  have hb := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ P2 b)).finitePiecewiseAffineOn hK
  have hh : FinitePiecewiseAffineOn (fun p : P2 => height b p.2) K.space := habs.max hb
  have hsign : FinitePiecewiseAffineOn
      (fun p : P2 => signedHeight b positive p.2) K.space := by
    cases positive with
    | false => exact (hh.postcomp (-ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
    | true => exact hh
  change K.space = source at hKs
  rw [← hKs]
  exact ⟨(hu.prod_mk hsign).prod_mk ht, (hsign.prod_mk hu).prod_mk ht⟩

theorem separated_pairs {b : ℝ} (hb : 0 < b) :
    (∀ p q : P2, 2 * b ≤ (strip b true p).1.2 - (strip b false q).1.2) ∧
      Disjoint (range (strip b true)) (range (strip b false)) ∧
      Disjoint (range (alternate b true)) (range (alternate b false)) := by
  have hgap (p q : P2) : 2 * b ≤ height b p.2 - -height b q.2 := by
    have hp : b ≤ height b p.2 := le_max_right _ _
    have hq : b ≤ height b q.2 := le_max_right _ _
    linarith
  have hne (p q : P2) : height b p.2 ≠ -height b q.2 := by
    intro heq
    have hbound := hgap p q
    linarith
  refine ⟨hgap, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · rintro z ⟨p, hp⟩ ⟨q, hq⟩
    exact hne p q (congrArg (fun w : C3 => w.1.2) (hp.trans hq.symm))
  · rintro z ⟨p, hp⟩ ⟨q, hq⟩
    exact hne p q (congrArg (fun w : C3 => w.1.1) (hp.trans hq.symm))

theorem eq_zero_of_outer {b : ℝ} (positive : Bool) (p : P2) (hp : b ≤ |p.2|) :
    strip b positive p = strip 0 positive p ∧
      alternate b positive p = alternate 0 positive p := by
  have h : height b p.2 = height 0 p.2 := by
    rw [height, height, max_eq_left hp, max_eq_left (abs_nonneg p.2)]
  constructor
  · simp only [strip, signedHeight, h]
  · simp only [alternate, signedHeight, h]

theorem arm_endpoints {b : ℝ} (hb : b < 1) (t : ℝ) :
    strip b true (t, -1) = ((-1, 1), t) ∧
      strip b true (t, 1) = ((1, 1), t) ∧
      strip b false (t, -1) = ((-1, -1), t) ∧
      strip b false (t, 1) = ((1, -1), t) ∧
      alternate b true (t, -1) = ((1, -1), t) ∧
      alternate b true (t, 1) = ((1, 1), t) ∧
      alternate b false (t, -1) = ((-1, -1), t) ∧
      alternate b false (t, 1) = ((-1, 1), t) := by
  simp [strip, alternate, signedHeight, height, max_eq_left hb.le]

theorem longitudinal_coordinate (b : ℝ) (positive : Bool) (p : P2) :
    (strip b positive p).2 = p.1 ∧ (alternate b positive p).2 = p.1 :=
  ⟨rfl, rfl⟩

theorem mapsTo_tube {b : ℝ} (hb : b ≤ 1) (positive : Bool) :
    MapsTo (strip b positive) source tube ∧ MapsTo (alternate b positive) source tube := by
  have hsign (p : P2) (hp : p ∈ source) : signedHeight b positive p.2 ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_signedHeight]
    exact max_le (abs_le.mpr hp.2) hb
  exact ⟨fun p hp => ⟨⟨hp.2, hsign p hp⟩, hp.1⟩,
    fun p hp => ⟨⟨hsign p hp, hp.2⟩, hp.1⟩⟩

theorem transverse_boundary_iff {b : ℝ} (hb : b < 1) (positive : Bool)
    {p : P2} (hp : p ∈ source) :
    (|(strip b positive p).1.1| = 1 ∨ |(strip b positive p).1.2| = 1 ↔ |p.2| = 1) ∧
      (|(alternate b positive p).1.1| = 1 ∨ |(alternate b positive p).1.2| = 1 ↔
        |p.2| = 1) := by
  have hh := height_eq_one_iff hb (abs_le.mpr hp.2)
  constructor
  · change (|p.2| = 1 ∨ |signedHeight b positive p.2| = 1) ↔ |p.2| = 1
    rw [abs_signedHeight, hh, or_self]
  · change (|signedHeight b positive p.2| = 1 ∨ |p.2| = 1) ↔ |p.2| = 1
    rw [abs_signedHeight, hh, or_self]

private theorem mem_frontier_tube_iff {z : C3} (hz : z ∈ tube) :
    z ∈ frontier tube ↔ z.2 = 0 ∨ z.2 = 1 ∨ (|z.1.1| = 1 ∨ |z.1.2| = 1) := by
  change z ∈ frontier ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) ↔ _
  simp only [frontier_prod_eq, closure_prod_eq, isClosed_Icc.closure_eq,
    frontier_Icc (show (-1 : ℝ) ≤ 1 by norm_num),
    frontier_Icc (show (0 : ℝ) ≤ 1 from zero_le_one),
    mem_union, mem_prod, mem_insert_iff, mem_singleton_iff,
    hz.1.1, hz.1.2, hz.2, true_and, and_true,
    abs_eq (show (0 : ℝ) ≤ 1 from zero_le_one)]
  tauto

theorem whole_boundary_iff {b : ℝ} (hb : b < 1) (positive : Bool)
    {p : P2} (hp : p ∈ source) :
    (strip b positive p ∈ frontier tube ↔ p.1 = 0 ∨ p.1 = 1 ∨ |p.2| = 1) ∧
      (alternate b positive p ∈ frontier tube ↔ p.1 = 0 ∨ p.1 = 1 ∨ |p.2| = 1) := by
  have hm := mapsTo_tube hb.le positive
  have ht := transverse_boundary_iff hb positive hp
  exact ⟨(mem_frontier_tube_iff (hm.1 hp)).trans
      (or_congr Iff.rfl (or_congr Iff.rfl ht.1)),
    (mem_frontier_tube_iff (hm.2 hp)).trans
      (or_congr Iff.rfl (or_congr Iff.rfl ht.2))⟩

private theorem mem_resolved_iff {b : ℝ} {z : C3} :
    z ∈ resolved b ↔ z.2 ∈ Icc (0 : ℝ) 1 ∧ z.1.1 ∈ Icc (-1 : ℝ) 1 ∧
      (z.1.2 = height b z.1.1 ∨ z.1.2 = -height b z.1.1) := by
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨hp.1, hp.2, Or.inl rfl⟩
    · exact ⟨hp.1, hp.2, Or.inr rfl⟩
  · rintro ⟨ht, hu, hy | hy⟩
    · exact Or.inl ⟨(z.2, z.1.1), ⟨ht, hu⟩, Prod.ext (Prod.ext rfl hy.symm) rfl⟩
    · exact Or.inr ⟨(z.2, z.1.1), ⟨ht, hu⟩, Prod.ext (Prod.ext rfl hy.symm) rfl⟩

private theorem mem_alternateResolved_iff {b : ℝ} {z : C3} :
    z ∈ alternateResolved b ↔ swapTransverse z ∈ resolved b := by
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨p, hp, rfl⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · have h' := congrArg swapTransverse h
      change alternate b true p = z at h'
      exact Or.inl ⟨p, hp, h'⟩
    · have h' := congrArg swapTransverse h
      change alternate b false p = z at h'
      exact Or.inr ⟨p, hp, h'⟩

private theorem swap_crossing_iff (z : C3) :
    swapTransverse z ∈ crossing ↔ z ∈ crossing := by
  have hdiag : (z.1.1 = z.1.2 ∨ z.1.1 = -z.1.2) ↔
      (z.1.2 = z.1.1 ∨ z.1.2 = -z.1.1) := by
    constructor <;> rintro (h | h)
    · exact Or.inl h.symm
    · right; linarith
    · exact Or.inl h.symm
    · right; linarith
  change (((z.1.2 ∈ Icc (-1 : ℝ) 1 ∧ z.1.1 ∈ Icc (-1 : ℝ) 1) ∧
    z.2 ∈ Icc (0 : ℝ) 1) ∧ (z.1.1 = z.1.2 ∨ z.1.1 = -z.1.2)) ↔
      (((z.1.1 ∈ Icc (-1 : ℝ) 1 ∧ z.1.2 ∈ Icc (-1 : ℝ) 1) ∧
        z.2 ∈ Icc (0 : ℝ) 1) ∧ (z.1.2 = z.1.1 ∨ z.1.2 = -z.1.1))
  rw [hdiag]
  tauto

private theorem swap_outer_iff (r : ℝ) (z : C3) :
    swapTransverse z ∈ outer r ↔ z ∈ outer r := by
  change r ≤ max |z.1.2| |z.1.1| ↔ r ≤ max |z.1.1| |z.1.2|
  rw [max_comm |z.1.2| |z.1.1|]

theorem resolved_outer_collar {b r : ℝ} (hbr : b < r) :
    resolved b ∩ outer r = crossing ∩ outer r := by
  ext z
  constructor
  · rintro ⟨hz, ho⟩
    obtain ⟨ht, hu, hy⟩ := mem_resolved_iff.mp hz
    have hyabs : |z.1.2| = height b z.1.1 := by
      rcases hy with h | h
      · rw [h, abs_of_nonneg (height_nonneg b z.1.1)]
      · rw [h, abs_neg, abs_of_nonneg (height_nonneg b z.1.1)]
    have hrh : r ≤ height b z.1.1 := by
      change r ≤ max |z.1.1| |z.1.2| at ho
      rw [hyabs] at ho
      exact ho.trans (max_le (le_max_left _ _) le_rfl)
    have hru : r ≤ |z.1.1| := by
      by_contra hn
      exact (not_lt_of_ge hrh) (max_lt (lt_of_not_ge hn) hbr)
    have hh : height b z.1.1 = |z.1.1| := max_eq_left (hbr.le.trans hru)
    have hyu : |z.1.2| = |z.1.1| := hyabs.trans hh
    have hv : z.1.2 ∈ Icc (-1 : ℝ) 1 :=
      abs_le.mp (hyu.le.trans (abs_le.mpr hu))
    exact ⟨⟨⟨⟨hu, hv⟩, ht⟩, abs_eq_abs.mp hyu⟩, ho⟩
  · rintro ⟨⟨hz, hdiag⟩, ho⟩
    have hyu : |z.1.2| = |z.1.1| := abs_eq_abs.mpr hdiag
    have hru : r ≤ |z.1.1| := by
      change r ≤ max |z.1.1| |z.1.2| at ho
      rwa [hyu, max_self] at ho
    have hh : height b z.1.1 = |z.1.1| := max_eq_left (hbr.le.trans hru)
    have hy : z.1.2 = height b z.1.1 ∨ z.1.2 = -height b z.1.1 := by
      rw [hh]
      exact (abs_eq (abs_nonneg z.1.1)).mp hyu
    exact ⟨mem_resolved_iff.mpr ⟨hz.2, hz.1.1, hy⟩, ho⟩

theorem alternate_outer_collar {b r : ℝ} (hbr : b < r) :
    alternateResolved b ∩ outer r = crossing ∩ outer r := by
  ext z
  have h := Set.ext_iff.mp (resolved_outer_collar hbr) (swapTransverse z)
  change (z ∈ alternateResolved b ∧ z ∈ outer r) ↔
    (z ∈ crossing ∧ z ∈ outer r)
  rw [mem_alternateResolved_iff, ← swap_outer_iff r z]
  simpa only [mem_inter_iff, swap_crossing_iff] using h

theorem reflection_equations (b : ℝ) (positive : Bool) (p : P2) :
    horizontalReflection (strip b positive p) = strip b (!positive) p ∧
      verticalReflection (strip b positive p) = strip b positive (p.1, -p.2) ∧
      verticalReflection (alternate b positive p) = alternate b (!positive) p ∧
      horizontalReflection (alternate b positive p) = alternate b positive (p.1, -p.2) ∧
      swapTransverse (strip b positive p) = alternate b positive p ∧
      swapTransverse (alternate b positive p) = strip b positive p := by
  cases positive <;>
    simp [strip, alternate, signedHeight, height, horizontalReflection,
      verticalReflection, swapTransverse]

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
