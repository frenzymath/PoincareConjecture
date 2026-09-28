import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcParameter
import Mathlib.Data.Nat.Dist

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem subarc_parameter_cover {k : ℕ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (k + 1 : ℕ)) :
    ∃ i : Fin (k + 1), t ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1) := by
  by_cases heq : t = (k + 1 : ℕ)
  · refine ⟨Fin.last k, ?_⟩
    rw [heq]
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one, mem_Icc]
    exact ⟨by linarith, le_rfl⟩
  · let j : ℤ := ⌊t⌋
    have hj0 : 0 ≤ j := Int.floor_nonneg.mpr ht.1
    have hjk : j < (k + 1 : ℕ) := by
      exact_mod_cast (Int.floor_le t).trans_lt (lt_of_le_of_ne ht.2 heq)
    let i : Fin (k + 1) := ⟨j.toNat, (Int.toNat_lt hj0).mpr hjk⟩
    have hval : (i.val : ℝ) = (j : ℝ) := by
      dsimp only [i]
      exact_mod_cast Int.toNat_of_nonneg hj0
    refine ⟨i, ?_⟩
    rw [hval]
    exact ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩

private theorem subarc_parameter_edge {k : ℕ} (p : Polygon E (k + 2))
    (i : Fin (k + 1)) {t : ℝ} (ht : t ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1)) :
    polygonLinearParameter p t = AffineMap.lineMap (p i.castSucc) (p i.succ)
      (t - i.val) := by
  have hi : polygonIntegerIndex (k + 2) (i.val : ℤ) = i.castSucc :=
    polygonIntegerIndex_nat i.castSucc
  have hnext : finRotate (k + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
  simpa only [hi, Int.cast_natCast, Polygon.edgePath, hnext] using
    polygonLinearParameter_eq_edge p (i.val : ℤ) (by simpa only [Int.cast_natCast] using ht)

private theorem subarc_image_sdiff_endpoints {n : ℕ} {p : Polygon E (n + 2)}
    (hp : IsSimplePolygonalArc p) (a b : Fin (n + 2)) :
    (polygonLinearParameter p '' Icc (min (a.val : ℝ) (b.val : ℝ))
      (max (a.val : ℝ) (b.val : ℝ))) \ {p a, p b} =
    polygonLinearParameter p '' Ioo (min (a.val : ℝ) (b.val : ℝ))
      (max (a.val : ℝ) (b.val : ℝ)) := by
  have hindex (i : Fin (n + 2)) : (i.val : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℕ) := by
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast (show i.val ≤ n + 1 from by omega)⟩
  have hinterval {t : ℝ}
      (ht : t ∈ Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ))) :
      t ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨(le_min (hindex a).1 (hindex b).1).trans ht.1,
      ht.2.trans (max_le (hindex a).2 (hindex b).2)⟩
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hnot⟩
    have hta : t ≠ (a.val : ℝ) := fun h =>
      hnot (Or.inl (h ▸ polygonLinearParameter_natVertex p a))
    have htb : t ≠ (b.val : ℝ) := fun h =>
      hnot (Or.inr (h ▸ polygonLinearParameter_natVertex p b))
    refine ⟨t, ?_, rfl⟩
    rcases le_total (a.val : ℝ) (b.val : ℝ) with hab | hba
    · simp only [min_eq_left hab, max_eq_right hab, mem_Icc, mem_Ioo] at ht ⊢
      exact ⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩
    · simp only [min_eq_right hba, max_eq_left hba, mem_Icc, mem_Ioo] at ht ⊢
      exact ⟨lt_of_le_of_ne ht.1 htb.symm, lt_of_le_of_ne ht.2 hta⟩
  · rintro ⟨t, ht, rfl⟩
    have hne : t ≠ (a.val : ℝ) ∧ t ≠ (b.val : ℝ) := by
      rcases le_total (a.val : ℝ) (b.val : ℝ) with hab | hba
      · simp only [min_eq_left hab, max_eq_right hab, mem_Ioo] at ht
        exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
      · simp only [min_eq_right hba, max_eq_left hba, mem_Ioo] at ht
        exact ⟨ne_of_lt ht.2, ne_of_gt ht.1⟩
    refine ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, ?_⟩
    rintro (ha | hb)
    · exact hne.1 (hp.injOn_polygonLinearParameter (hinterval ⟨ht.1.le, ht.2.le⟩)
        (hindex a) (ha.trans (polygonLinearParameter_natVertex p a).symm))
    · exact hne.2 (hp.injOn_polygonLinearParameter (hinterval ⟨ht.1.le, ht.2.le⟩)
        (hindex b) (hb.trans (polygonLinearParameter_natVertex p b).symm))

theorem IsSimplePolygonalArc.exists_consecutive_subarc {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (a b : Fin (n + 2)) (hab : a ≠ b) :
    ∃ k : ℕ, ∃ q : Polygon E (k + 2), k + 1 = Nat.dist a.val b.val ∧
      IsSimplePolygonalArc q ∧ q 0 = p a ∧ q (Fin.last (k + 1)) = p b ∧
      (∀ j : Fin (k + 2), q j = polygonLinearParameter p
        (if a < b then (a.val : ℝ) + j.val else (a.val : ℝ) - j.val)) ∧
      (∀ t ∈ Icc (0 : ℝ) (k + 1 : ℕ), polygonLinearParameter q t =
        polygonLinearParameter p (if a < b then (a.val : ℝ) + t else (a.val : ℝ) - t)) ∧
      polygonArcBoundary q = polygonLinearParameter p ''
        Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) ∧
      polygonArcBoundary q \ {p a, p b} = polygonLinearParameter p ''
        Ioo (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) := by
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hdpos := Nat.dist_pos_of_ne habv
  let k := Nat.dist a.val b.val - 1
  have hk : k + 1 = Nat.dist a.val b.val := by dsimp only [k]; omega
  have hinc (h : a < b) : a.val + (k + 1) = b.val := by
    rw [Nat.dist_eq_sub_of_le (show a.val ≤ b.val from h.le)] at hk
    omega
  have hdec (h : ¬ a < b) : b.val + (k + 1) = a.val := by
    rw [Nat.dist_eq_sub_of_le_right (show b.val ≤ a.val from le_of_not_gt h)] at hk
    omega
  let f : Fin (k + 2) → Fin (n + 2) := fun j =>
    ⟨if a < b then a.val + j.val else a.val - j.val, by
      split_ifs with h
      · have := hinc h
        omega
      · have := hdec h
        omega⟩
  let e : Fin (k + 1) → Fin (n + 1) := fun j =>
    ⟨if a < b then a.val + j.val else a.val - j.val - 1, by
      split_ifs with h
      · have := hinc h
        omega
      · have := hdec h
        omega⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have hval := congrArg Fin.val hij
    apply Fin.ext
    by_cases h : a < b
    · simp only [f, if_pos h] at hval
      omega
    · simp only [f, if_neg h] at hval
      have := hdec h
      omega
  have heinj : Function.Injective e := by
    intro i j hij
    have hval := congrArg Fin.val hij
    apply Fin.ext
    by_cases h : a < b
    · simp only [e, if_pos h] at hval
      omega
    · simp only [e, if_neg h] at hval
      have := hdec h
      omega
  have hfirst : f 0 = a := by
    apply Fin.ext
    simp only [f, Fin.val_zero, add_zero, Nat.sub_zero, ite_self]
  have hlast : f (Fin.last (k + 1)) = b := by
    apply Fin.ext
    by_cases h : a < b
    · simp only [f, if_pos h, Fin.val_last]
      exact hinc h
    · simp only [f, if_neg h, Fin.val_last]
      have := hdec h
      omega
  have hincends (h : a < b) (j : Fin (k + 1)) :
      f j.castSucc = (e j).castSucc ∧ f j.succ = (e j).succ := by
    constructor <;> apply Fin.ext <;>
      simp only [f, e, if_pos h, Fin.val_castSucc, Fin.val_succ]
    omega
  have hdecends (h : ¬ a < b) (j : Fin (k + 1)) :
      f j.castSucc = (e j).succ ∧ f j.succ = (e j).castSucc := by
    have := hdec h
    constructor <;> apply Fin.ext <;>
      simp only [f, e, if_neg h, Fin.val_castSucc, Fin.val_succ] <;> omega
  let q : Polygon E (k + 2) := ⟨fun j => p (f j)⟩
  have hedge (j : Fin (k + 1)) : q.edgeSet ℝ j.castSucc = p.edgeSet ℝ (e j).castSucc := by
    rw [polygon_arcEdge_eq_segment, polygon_arcEdge_eq_segment]
    change segment ℝ (p (f j.castSucc)) (p (f j.succ)) = _
    by_cases h : a < b
    · rw [(hincends h j).1, (hincends h j).2]
    · rw [(hdecends h j).1, (hdecends h j).2, segment_symm]
  have hends (j : Fin (k + 1)) :
      ({q j.castSucc, q j.succ} : Set E) = {p (e j).castSucc, p (e j).succ} := by
    change ({p (f j.castSucc), p (f j.succ)} : Set E) = _
    by_cases h : a < b
    · rw [(hincends h j).1, (hincends h j).2]
    · rw [(hdecends h j).1, (hdecends h j).2, pair_comm]
  have hq : IsSimplePolygonalArc q := by
    refine ⟨hp.vertices_injective.comp hfinj, ?_⟩
    intro i j hij x hx
    rw [hedge i, hedge j] at hx
    rw [hends i, hends j]
    exact hp.edges_inter _ _ (fun h => hij (heinj h)) hx
  have hvertices (j : Fin (k + 2)) : q j = polygonLinearParameter p
      (if a < b then (a.val : ℝ) + j.val else (a.val : ℝ) - j.val) := by
    change p (f j) = _
    rw [← polygonLinearParameter_natVertex p (f j)]
    congr 1
    by_cases h : a < b
    · simp only [f, if_pos h, Nat.cast_add]
    · have hj : j.val ≤ a.val := by have := hdec h; omega
      simp only [f, if_neg h, Nat.cast_sub hj]
  have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (k + 1 : ℕ)) :
      polygonLinearParameter q t = polygonLinearParameter p
        (if a < b then (a.val : ℝ) + t else (a.val : ℝ) - t) := by
    obtain ⟨i, hi⟩ := subarc_parameter_cover ht
    by_cases h : a < b
    · have heval : ((e i).val : ℝ) = (a.val : ℝ) + i.val := by
        simp only [e, if_pos h, Nat.cast_add]
      have hint : (a.val : ℝ) + t ∈ Icc ((e i).val : ℝ) (((e i).val : ℝ) + 1) := by
        rw [heval]
        constructor <;> linarith [hi.1, hi.2]
      rw [if_pos h, subarc_parameter_edge q i hi, subarc_parameter_edge p (e i) hint]
      change AffineMap.lineMap (p (f i.castSucc)) (p (f i.succ)) (t - i.val) = _
      rw [(hincends h i).1, (hincends h i).2, heval]
      congr 1
      ring
    · have hiA : i.val + 1 ≤ a.val := by have := hdec h; omega
      have heval : ((e i).val : ℝ) = (a.val : ℝ) - i.val - 1 := by
        simp only [e, if_neg h, Nat.cast_sub (show 1 ≤ a.val - i.val from by omega),
          Nat.cast_sub (show i.val ≤ a.val from by omega), Nat.cast_one]
      have hint : (a.val : ℝ) - t ∈ Icc ((e i).val : ℝ) (((e i).val : ℝ) + 1) := by
        rw [heval]
        constructor <;> linarith [hi.1, hi.2]
      rw [if_neg h, subarc_parameter_edge q i hi, subarc_parameter_edge p (e i) hint]
      change AffineMap.lineMap (p (f i.castSucc)) (p (f i.succ)) (t - i.val) = _
      rw [(hdecends h i).1, (hdecends h i).2, heval]
      rw [show (a.val : ℝ) - t - ((a.val : ℝ) - i.val - 1) = 1 - (t - i.val) by ring]
      exact (AffineMap.lineMap_apply_one_sub _ _ _).symm
  have himage : (fun t : ℝ => if a < b then (a.val : ℝ) + t else (a.val : ℝ) - t) ''
      Icc (0 : ℝ) (k + 1 : ℕ) =
      Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) := by
    by_cases h : a < b
    · have habR : (a.val : ℝ) ≤ b.val := by exact_mod_cast h.le
      have hlength : (a.val : ℝ) + (k + 1 : ℕ) = b.val := by exact_mod_cast hinc h
      simp only [if_pos h, min_eq_left habR, max_eq_right habR]
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        constructor <;> linarith [hu.1, hu.2]
      · intro ht
        exact ⟨t - a.val, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by ring⟩
    · have habR : (b.val : ℝ) ≤ a.val := by exact_mod_cast le_of_not_gt h
      have hlength : (b.val : ℝ) + (k + 1 : ℕ) = a.val := by exact_mod_cast hdec h
      simp only [if_neg h, min_eq_right habR, max_eq_left habR]
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        constructor <;> linarith [hu.1, hu.2]
      · intro ht
        exact ⟨a.val - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by ring⟩
  have hboundary : polygonArcBoundary q = polygonLinearParameter p ''
      Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) := by
    rw [← image_polygonLinearParameter_arc q, ← himage, image_image]
    exact image_congr hparameter
  refine ⟨k, q, hk, hq, ?_, ?_, hvertices, hparameter, hboundary, ?_⟩
  · change p (f 0) = p a
    rw [hfirst]
  · change p (f (Fin.last (k + 1))) = p b
    rw [hlast]
  · rw [hboundary]
    exact subarc_image_sdiff_endpoints hp a b

end PoincareConjecture.M25.Topology3D
