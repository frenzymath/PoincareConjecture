import PoincareConjecture.Proofs.M25.Topology3D.Polygon.TriangleRegion
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.NoninterlacingMatching
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcTerminalMatching

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem triangle_free_midpoint_not_mem_interior
    (r : Polygon E 3) (hr : IsSimplePolygon r) (hdim : Module.finrank ℝ E = 2)
    (f : E ≃ᴬ[ℝ] ℝ × ℝ) (w : E) (hzero : f (r 0) = (0, 0))
    (hpos : 0 < (f (r 1)).1 ∧ 0 < (f (r 1)).2)
    (hlast : (f (r 2) = (1, 0) ∧ f w = (0, 1)) ∨
      (f (r 2) = (0, 1) ∧ f w = (1, 0))) :
    AffineMap.lineMap (r 0) w (1 / 2 : ℝ) ∉ polygonInterior r := by
  have hsep (L : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ i, 0 ≤ L (f (r i)))
      (hw : L (f w) < 0) :
      AffineMap.lineMap (r 0) w (1 / 2 : ℝ) ∉ polygonInterior r := by
    intro hx
    have hxH : AffineMap.lineMap (r 0) w (1 / 2 : ℝ) ∈ convexHull ℝ (range r) :=
      hr.triangle_closure_polygonInterior hdim ▸ subset_closure hx
    have hxF : f (AffineMap.lineMap (r 0) w (1 / 2 : ℝ)) ∈
        convexHull ℝ (f.toAffineMap '' range r) := by
      rw [← f.toAffineMap.image_convexHull]
      exact mem_image_of_mem f hxH
    have hgen : f.toAffineMap '' range r ⊆ {x | 0 ≤ L x} := by
      rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
      exact hL i
    have hnonneg := convexHull_min hgen (convex_halfSpace_ge L.isLinear 0) hxF
    have hmid : f (AffineMap.lineMap (r 0) w (1 / 2 : ℝ)) =
        AffineMap.lineMap (0, 0) (f w) (1 / 2 : ℝ) := by
      change f.toAffineMap (AffineMap.lineMap (r 0) w (1 / 2 : ℝ)) = _
      rw [f.toAffineMap.apply_lineMap]
      change AffineMap.lineMap (f (r 0)) (f w) (1 / 2 : ℝ) = _
      rw [hzero]
    change 0 ≤ L (f (AffineMap.lineMap (r 0) w (1 / 2 : ℝ))) at hnonneg
    rw [hmid] at hnonneg
    have hh : L (AffineMap.lineMap (0, 0) (f w) (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) * L (f w) := by
      rw [AffineMap.lineMap_apply_module]
      simp only [show (0, 0) = (0 : ℝ × ℝ) from rfl, smul_zero, zero_add,
        map_smul, smul_eq_mul]
    rw [hh] at hnonneg
    linarith
  rcases hlast with ⟨hlast, hw⟩ | ⟨hlast, hw⟩
  · let L : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
      (f (r 1)).2 • LinearMap.fst ℝ ℝ ℝ - (f (r 1)).1 • LinearMap.snd ℝ ℝ ℝ
    apply hsep L
    · intro i
      fin_cases i
      · change 0 ≤ L (f (r 0))
        rw [hzero]
        simp [L]
      · change 0 ≤ (f (r 1)).2 * (f (r 1)).1 - (f (r 1)).1 * (f (r 1)).2
        nlinarith
      · change 0 ≤ L (f (r 2))
        rw [hlast]
        simpa [L] using hpos.2.le
    · rw [hw]
      simpa [L] using neg_neg_of_pos hpos.1
  · let L : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
      (f (r 1)).1 • LinearMap.snd ℝ ℝ ℝ - (f (r 1)).2 • LinearMap.fst ℝ ℝ ℝ
    apply hsep L
    · intro i
      fin_cases i
      · change 0 ≤ L (f (r 0))
        rw [hzero]
        simp [L]
      · change 0 ≤ (f (r 1)).1 * (f (r 1)).2 - (f (r 1)).2 * (f (r 1)).1
        nlinarith
      · change 0 ≤ L (f (r 2))
        rw [hlast]
        simpa [L] using hpos.1.le
    · rw [hw]
      simpa [L] using neg_neg_of_pos hpos.2

private theorem exists_positive_terminal_matched_edge {k : ℕ} (hk : 2 ≤ k)
    (U V : Prop) [Decidable U] [Decidable V]
    (e : Fin (k - 1 + (if U then 1 else 0) + (if V then 1 else 0)) ↪ Fin (k + 1))
    (he : ∀ i, (e i).val = (if U then 0 else 1) + i.val)
    (M : Fin (k - 1 + (if U then 1 else 0) + (if V then 1 else 0)) →
      Fin (k - 1 + (if U then 1 else 0) + (if V then 1 else 0)))
    (hM : IsNoninterlacingMatching M)
    (heven : Even (k - 1 + (if U then 1 else 0) + (if V then 1 else 0)))
    (htwo : 2 ≤ k - 1 + (if U then 1 else 0) + (if V then 1 else 0))
    (htri : U → k ≠ 2) :
    ∃ a b, M a = b ∧ 0 < (e a).val ∧ (e a).val + 1 = (e b).val := by
  by_cases hU : U
  · have hthree : 3 ≤ k := by have hh := htri hU; omega
    have hfour : 4 ≤ k - 1 + (if U then 1 else 0) + (if V then 1 else 0) := by
      obtain ⟨a, ha⟩ := heven
      by_cases hV : V
      · simp only [if_pos hU, if_pos hV] at ha ⊢
        omega
      · simp only [if_pos hU, if_neg hV] at ha ⊢
        omega
    obtain ⟨a, b, ha, hab, hMa⟩ := hM.exists_adjacent_away_first hfour
    refine ⟨a, b, hMa, ?_, ?_⟩
    · simpa only [he, if_pos hU, zero_add] using ha
    · simpa only [he, if_pos hU, zero_add] using hab
  · obtain ⟨a, b, hab, hMa⟩ := hM.exists_adjacent (by omega)
    refine ⟨a, b, hMa, ?_, ?_⟩
    · rw [he, if_neg hU]
      omega
    · rw [he, he, if_neg hU]
      omega

theorem IsSimplePolygonalArc.exists_terminal_path_good_subarc {n k : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hdim : Module.finrank ℝ E = 2) (hk : 2 ≤ k)
    (c : Fin (k + 1) ↪ Fin (n + 2))
    (hint : ∀ i, c i ≠ 0 ∧ c i ≠ Fin.last (n + 1))
    (hadj : c (Fin.last k) = (finRotate (n + 2)).symm (c 0) ∨
      c (Fin.last k) = finRotate (n + 2) (c 0))
    (hwnot : (if c (Fin.last k) = (finRotate (n + 2)).symm (c 0)
      then finRotate (n + 2) (c 0) else (finRotate (n + 2)).symm (c 0)) ∉ range c)
    (f : E ≃ᴬ[ℝ] ℝ × ℝ) (hf0 : f (p (c 0)) = (0, 0))
    (hfpre : f (p ((finRotate (n + 2)).symm (c 0))) = (1, 0))
    (hfsuc : f (p (finRotate (n + 2) (c 0))) = (0, 1))
    (hfpos : 0 < (f (p (c ⟨1, by omega⟩))).1 ∧
      0 < (f (p (c ⟨1, by omega⟩))).2) :
    let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
    let u := c 0
    let v := c (Fin.last k)
    let w := if v = (finRotate (n + 2)).symm u then finRotate (n + 2) u
      else (finRotate (n + 2)).symm u
    let I := polygonInterior r
    let O := polygonExterior r
    IsSimplePolygon r →
    r.boundary ℝ ∩ polygonArcBoundary p = range r ∪ segment ℝ (p v) (p u) →
    p 0 ∈ O → p (Fin.last (n + 1)) ∈ O →
    (∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k →
      ∃ ε : ℝ, 0 < ε ∧ ∃ W A B : Set E,
        IsOpen W ∧ r i ∈ W ∧ IsPreconnected A ∧ IsPreconnected B ∧
        A ∪ B = W \ r.boundary ℝ ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
          (p ((finRotate (n + 2)).symm (c i))) t ∈ A) ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
          (p (finRotate (n + 2) (c i))) t ∈ B)) →
    (∀ j : Fin k, Disjoint
      (openSegment ℝ (p (c j.castSucc)) (p (c j.succ))) (polygonArcBoundary p)) →
    ∃ j : Fin k, 0 < j.val ∧
      let T := polygonLinearParameter p '' Icc
        (min ((c j.castSucc).val : ℝ) ((c j.succ).val : ℝ))
        (max ((c j.castSucc).val : ℝ) ((c j.succ).val : ℝ))
      let S := polygonLinearParameter p '' Ioo
        (min ((c j.castSucc).val : ℝ) ((c j.succ).val : ℝ))
        (max ((c j.castSucc).val : ℝ) ((c j.succ).val : ℝ))
      S ⊆ I ∧ T ∩ r.boundary ℝ = {r j.castSucc, r j.succ} ∧
      p w ∉ T ∧ p v ∉ S ∧
      Disjoint (openSegment ℝ (p (c j.castSucc)) (p (c j.succ)))
        (polygonArcBoundary p) ∧
      ∃ ell : ℕ, ∃ q : Polygon E (ell + 2),
        ell + 1 = Nat.dist (c j.castSucc).val (c j.succ).val ∧
        IsSimplePolygonalArc q ∧ q 0 = p (c j.castSucc) ∧
        q (Fin.last (ell + 1)) = p (c j.succ) ∧
        (∀ i : Fin (ell + 2), q i = polygonLinearParameter p
          (if c j.castSucc < c j.succ then ((c j.castSucc).val : ℝ) + i.val
            else ((c j.castSucc).val : ℝ) - i.val)) ∧
        (∀ t ∈ Icc (0 : ℝ) (ell + 1 : ℕ), polygonLinearParameter q t =
          polygonLinearParameter p (if c j.castSucc < c j.succ
            then ((c j.castSucc).val : ℝ) + t else ((c j.castSucc).val : ℝ) - t)) ∧
        polygonArcBoundary q = T ∧
        polygonArcBoundary q \ {p (c j.castSucc), p (c j.succ)} = S := by
  classical
  dsimp only
  intro hr hcontact hfirst hlast hcross hvis
  let r : Polygon E (k + 1) := ⟨fun i => p (c i)⟩
  let u := c 0
  let v := c (Fin.last k)
  let w := if v = (finRotate (n + 2)).symm u then finRotate (n + 2) u
    else (finRotate (n + 2)).symm u
  let z := if v = (finRotate (n + 2)).symm u then (finRotate (n + 2)).symm v
    else finRotate (n + 2) v
  let U := AffineMap.lineMap (p u) (p w) (1 / 2 : ℝ) ∈ polygonInterior r
  let V := AffineMap.lineMap (p v) (p z) (1 / 2 : ℝ) ∈ polygonInterior r
  let m := k - 1 + (if U then 1 else 0) + (if V then 1 else 0)
  have htri : U → k ≠ 2 := by
    intro hU hk2
    subst k
    have hend : (f (r 2) = (1, 0) ∧ f (p w) = (0, 1)) ∨
        (f (r 2) = (0, 1) ∧ f (p w) = (1, 0)) := by
      by_cases h : c (Fin.last 2) = (finRotate (n + 2)).symm (c 0)
      · left
        constructor
        · change f (p (c (Fin.last 2))) = (1, 0)
          rw [h]
          exact hfpre
        · dsimp only [w, v, u]
          rw [if_pos h]
          exact hfsuc
      · right
        constructor
        · change f (p (c (Fin.last 2))) = (0, 1)
          rw [hadj.resolve_left h]
          exact hfsuc
        · dsimp only [w, v, u]
          rw [if_neg h]
          exact hfpre
    exact triangle_free_midpoint_not_mem_interior r hr hdim f (p w) hf0 hfpos hend hU
  obtain ⟨e, he, M, hM, heven, htwo, _, hwO, hwI, hinside, hmeet, hq,
    hdis, _, _, _⟩ := hp.exists_terminal_path_inside_matching hdim hk c hint hadj hwnot
      hr hcontact hfirst hlast hcross
  obtain ⟨a, b, hMa, hapos, hab⟩ :=
    exists_positive_terminal_matched_edge hk U V e he M hM heven htwo htri
  let j : Fin k := ⟨(e a).val, by have hh := (e b).isLt; omega⟩
  have hj0 : j.castSucc = e a := Fin.ext rfl
  have hj1 : j.succ = e b := Fin.ext hab
  let T := fun i => polygonLinearParameter p '' Icc
    (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
    (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
  let S := fun i => polygonLinearParameter p '' Ioo
    (min ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
    (max ((c (e i)).val : ℝ) ((c (e (M i))).val : ℝ))
  have hST (i : Fin m) : S i ⊆ T i := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hwne (i : Fin (k + 1)) : p w ≠ r i := by
    intro hh
    exact hwnot ⟨i, hp.vertices_injective hh.symm⟩
  have hw : p w ∉ T a := by
    by_cases hU : U
    · let i0 : Fin m := ⟨0, by omega⟩
      have he0 : e i0 = 0 := by
        apply Fin.ext
        have hh : (e i0).val = (if U then 0 else 1) + i0.val := he i0
        simpa only [if_pos hU, zero_add, i0, Fin.val_zero] using hh
      have h0a : i0 ≠ a := by
        intro hh
        have hv := congrArg Fin.val (congrArg e hh)
        rw [he0] at hv
        simp only [Fin.val_zero] at hv
        omega
      have h0b : i0 ≠ M a := by
        intro hh
        have hv := congrArg Fin.val (congrArg e hh)
        rw [he0, hMa] at hv
        simp only [Fin.val_zero] at hv
        omega
      exact fun hx => Set.disjoint_left.mp (hdis a i0 h0a h0b) hx
        (hST i0 (hwI i0 he0))
    · intro hx
      obtain ⟨ell, q, _, _, _, _, _, _, hT, hS⟩ := hq a
      have hpair : p w ∉ ({p (c (e a)), p (c (e (M a)))} : Set E) := by
        simpa only [mem_insert_iff, mem_singleton_iff, not_or] using
          And.intro (hwne (e a)) (hwne (e (M a)))
      have hqw : p w ∈ polygonArcBoundary q := by rw [hT]; exact hx
      have hsw : p w ∈ S a := by
        change polygonArcBoundary q \ {p (c (e a)), p (c (e (M a)))} = S a at hS
        rw [← hS]
        exact ⟨hqw, hpair⟩
      have hin := hinside a hsw
      exact (hwO hU).2 hin.2
  have hv : p v ∉ S a := fun hx =>
    (hinside a hx).1 (polygon_vertex_mem_boundary r (Fin.last k))
  refine ⟨j, hapos, ?_, ?_, ?_, ?_, hvis j, ?_⟩
  · simpa only [hj0, hj1, ← hMa] using hinside a
  · simpa only [hj0, hj1, ← hMa] using hmeet a
  · simpa only [hj0, hj1, ← hMa] using hw
  · simpa only [hj0, hj1, ← hMa] using hv
  · simpa only [hj0, hj1, ← hMa] using hq a

end PoincareConjecture.M25.Topology3D
