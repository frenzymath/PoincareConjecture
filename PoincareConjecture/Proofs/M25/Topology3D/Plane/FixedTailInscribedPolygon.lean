import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineTube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineChords
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineInscribedPolygon
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

private theorem exists_fine_affine_open_mesh {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ m : Fin (n + 3) → ℝ,
      StrictMono m ∧ m 0 = -r ∧ m (Fin.last (n + 2)) = r ∧
      (∀ v, m v = -r + (v.val : ℝ) * (2 * r / (n + 2))) ∧
      2 * r / (n + 2) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * r / ε)
  have hden : (0 : ℝ) < n + 2 := by positivity
  let h : ℝ := 2 * r / (n + 2)
  have hh : 0 < h := div_pos (by positivity) hden
  have hhε : h < ε := by
    apply (div_lt_iff₀ hden).mpr
    have hn' : 2 * r / ε < n + 2 := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hn'
  refine ⟨n, fun v => -r + (v.val : ℝ) * h, ?_, ?_, ?_, fun _ => rfl, hhε⟩
  · intro i j hij
    change -r + (i.val : ℝ) * h < -r + (j.val : ℝ) * h
    have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith [mul_lt_mul_of_pos_right hij' hh]
  · simp
  · change -r + ((n + 2 : ℕ) : ℝ) * (2 * r / (n + 2)) = r
    push_cast
    field_simp
    ring

private theorem simple_axis_mesh {n : ℕ} (p : Polygon (ℝ × ℝ) (n + 2))
    (m : Fin (n + 2) → ℝ) (hm : StrictMono m) (hp : ∀ v, p v = (m v, 0)) :
    IsSimplePolygonalArc p := by
  have he (i : Fin (n + 1)) (t : ℝ) :
      (p.edgePath ℝ i.castSucc t).1 =
        t * (m i.succ - m i.castSucc) + m i.castSucc := by
    have hi : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
    simp [Polygon.edgePath, hi, hp, AffineMap.lineMap_apply_module']
  have hmono (i : Fin (n + 1)) :
      StrictMonoOn (fun t : ℝ => (p.edgePath ℝ i.castSucc t).1) (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    change (p.edgePath ℝ i.castSucc a).1 < (p.edgePath ℝ i.castSucc b).1
    rw [he, he]
    have hmul := mul_lt_mul_of_pos_right hab
      (sub_pos.mpr (hm (show i.castSucc < i.succ from Nat.lt_succ_self _)))
    linarith
  refine (isSimplePolygonalArc_and_bijOn_of_ordered_projection p Prod.fst m hm
    (fun v => by rw [hp]) hmono ?_).1
  intro i
  have hc : ContinuousOn (fun t : ℝ => (p.edgePath ℝ i.castSucc t).1)
      (Icc (0 : ℝ) 1) := by
    simp_rw [he]
    exact ((continuous_id.mul continuous_const).add continuous_const).continuousOn
  simpa only [he, zero_mul, zero_add, one_mul, sub_add_cancel] using
    hc.image_Icc_of_monotoneOn (by norm_num) (hmono i).monotoneOn

theorem exists_fixedTail_openLine_inscribed_polygon_fine
    (C : ℝ × ℝ → ℝ × ℝ) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hC : ContDiff ℝ ∞ C)
    (hinj : ∀ z, Injective (fun u : ℝ => C (z, u)))
    (hreg : ∀ z u : ℝ, fderiv ℝ (fun v : ℝ => C (z, v)) u 1 ≠ 0)
    (htail : ∀ z u, R ≤ |u| → C (z, u) = (u, 0))
    (hstat : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ u, C (z, u) = (u, 0)) :
    ∃ n : ℕ, ∃ R' : ℝ, R < R' ∧ ∃ m : Fin (n + 3) → ℝ,
      StrictMono m ∧ m 0 = -R' ∧ m (Fin.last (n + 2)) = R' ∧
      (∀ v, m v = -R' + (v.val : ℝ) * (2 * R' / (n + 2))) ∧
      2 * R' / (n + 2) < ε ∧
      ∃ P : ℝ → Polygon (ℝ × ℝ) (n + 3),
        (∀ z v, P z v = C (z, m v)) ∧
        ∀ z, IsSimplePolygonalArc (P z) ∧ P z 0 = ((-R', 0) : ℝ × ℝ) ∧
          P z (Fin.last (n + 2)) = ((R', 0) : ℝ × ℝ) ∧
          ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
            LinearMap.fst ℝ ℝ ℝ ((-R', 0) : ℝ × ℝ) <
              LinearMap.fst ℝ ℝ ℝ (P z v) ∧
            LinearMap.fst ℝ ℝ ℝ (P z v) <
              LinearMap.fst ℝ ℝ ℝ ((R', 0) : ℝ × ℝ) := by
  let C0 : ((ℝ × ℝ) × ℝ) → ℝ × ℝ := fun p => C (p.1.1, p.2)
  have hC0 : ContDiff ℝ ∞ C0 :=
    hC.comp (contDiff_fst.fst.prodMk contDiff_snd)
  obtain ⟨η, hη, _, w, hw, _, T, hTs, hTf, _, hTi, _⟩ :=
    exists_fixedTail_openLine_normalTube C0 (a := 0) (b := 1) (c := 0) (d := 0)
      (by norm_num) le_rfl hR hC0 (fun z _ => hinj z.1)
      (fun z _ u => hreg z.1 u) (fun z u hu => htail z.1 u hu)
  have hsource (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (u : ℝ) :
      ((z, (0 : ℝ)), (u, (0 : ℝ))) ∈ T.source := by
    rw [hTs]
    exact ⟨⟨⟨by linarith [hz.1], by linarith [hz.2]⟩,
      ⟨by linarith, by linarith⟩⟩, by simpa using hw⟩
  have hzero (z u : ℝ) : T ((z, (0 : ℝ)), (u, (0 : ℝ))) = ((z, 0), C (z, u)) := by
    rw [hTf]
    simp [C0]
  have htgt (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (u : ℝ) :
      ((z, 0), C (z, u)) ∈ T.target := by
    rw [← hzero]
    exact T.map_source (hsource z hz u)
  have hinv (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (u : ℝ) :
      T.symm ((z, 0), C (z, u)) = ((z, 0), (u, 0)) := by
    rw [← hzero]
    exact T.left_inv (hsource z hz u)
  have hcompact : IsCompact (C '' (Icc (0 : ℝ) 1 ×ˢ Icc (-R) R)) :=
    (isCompact_Icc.prod isCompact_Icc).image hC.continuous
  obtain ⟨B, hB0, hB⟩ := hcompact.isBounded.exists_pos_norm_lt
  let R' := R + B + 1
  have hRR : R < R' := by dsimp [R']; linarith
  have hBR : B < R' := by dsimp [R']; linarith
  have hR' : 0 < R' := hR.trans hRR
  let D : ℝ × ℝ → ℝ × ℝ := fun p => fderiv ℝ (fun v => C (p.1, v)) p.2 1
  have hD : ContDiff ℝ ∞ D := by
    have hunc : ContDiff ℝ ∞
        (Function.uncurry (fun p : ℝ × ℝ => fun u => C (p.1, u))) :=
      hC.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact hunc.fderiv_apply (n := ∞) contDiff_snd contDiff_const (by simp)
  have hd (z u : ℝ) : HasDerivAt (fun v => C (z, v)) (D (z, u)) u :=
    ((hC.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp) u).hasFDerivAt.hasDerivAt
  obtain ⟨δ, hδ, hchord⟩ := exists_uniform_monotone_openLine_chords T hTi
    (K := Icc (0 : ℝ) 1) isCompact_Icc (l := -R') (u := R')
    (c := fun z u => C (z, u)) (d := fun z u => D (z, u))
    hC.continuous.continuousOn (fun z _ u _ => hd z u) hD.continuous.continuousOn
    (fun z hz u _ => htgt z hz u)
    (fun z hz u => by rw [hinv z hz u])
    (fun z hz u _ => by rw [hinv z hz u]) hw
  obtain ⟨n, m, hm, hm0, hmN, hmform, hmesh⟩ :=
    exists_fine_affine_open_mesh hR' (lt_min hδ hε)
  have hmI (v : Fin (n + 3)) : m v ∈ Icc (-R') R' := by
    constructor
    · rw [← hm0]
      exact hm.monotone (Fin.zero_le v)
    · rw [← hmN]
      exact hm.monotone (Fin.le_last v)
  have hgap (i : Fin (n + 2)) : m i.succ - m i.castSucc < δ := by
    rw [hmform, hmform]
    have hs : (((i.succ).val : ℕ) : ℝ) = (i.val : ℝ) + 1 := by simp
    rw [hs]
    change -R' + ((i.val : ℝ) + 1) * (2 * R' / (n + 2)) -
      (-R' + (i.val : ℝ) * (2 * R' / (n + 2))) < δ
    have hδ' := hmesh.trans_le (min_le_left δ ε)
    nlinarith
  let P : ℝ → Polygon (ℝ × ℝ) (n + 3) := fun z => ⟨fun v => C (z, m v)⟩
  have hedge (z : ℝ) (i : Fin (n + 2)) :
      (P z).edgePath ℝ i.castSucc =
        AffineMap.lineMap (C (z, m i.castSucc)) (C (z, m i.succ)) := by
    have hi : finRotate (n + 3) i.castSucc = i.succ := finRotate_of_lt i.isLt
    simp only [Polygon.edgePath, hi, P]
  have hsimple (z : ℝ) : IsSimplePolygonalArc (P z) := by
    by_cases hz : z ∈ Icc (0 : ℝ) 1
    · have hch (i : Fin (n + 2)) := hchord z hz (m i.castSucc) (hmI i.castSucc)
        (m i.succ) (hmI i.succ) (hm (show i.castSucc < i.succ from Nat.lt_succ_self _))
        (hgap i)
      refine (isSimplePolygonalArc_and_bijOn_of_ordered_projection (P z)
        (fun y => (T.symm ((z, 0), y)).2.1) m hm ?_ ?_ ?_).1
      · intro v
        change (T.symm ((z, 0), C (z, m v))).2.1 = m v
        rw [hinv z hz (m v)]
      · intro i
        simpa only [hedge] using (hch i).2.1
      · intro i
        simpa only [hedge] using (hch i).2.2
    · apply simple_axis_mesh (P z) m hm
      intro v
      have hz' : z ≤ 0 ∨ 1 ≤ z := by
        simp only [mem_Icc, not_and_or, not_le] at hz
        exact hz.imp le_of_lt le_of_lt
      exact hstat z hz' (m v)
  refine ⟨n, R', hRR, m, hm, hm0, hmN, hmform,
    hmesh.trans_le (min_le_right δ ε), P, fun _ _ => rfl, ?_⟩
  intro z
  refine ⟨hsimple z, ?_, ?_, ?_⟩
  · change C (z, m 0) = (-R', 0)
    rw [hm0]
    exact htail z (-R') (by simpa only [abs_neg, abs_of_pos hR'] using hRR.le)
  · change C (z, m (Fin.last (n + 2))) = (R', 0)
    rw [hmN]
    exact htail z R' (by simpa only [abs_of_pos hR'] using hRR.le)
  · intro v hv0 hvN
    have hvlo : -R' < m v := by
      rw [← hm0]
      exact hm (lt_of_le_of_ne (Fin.zero_le v) (Ne.symm hv0))
    have hvhi : m v < R' := by
      rw [← hmN]
      exact hm (lt_of_le_of_ne (Fin.le_last v) hvN)
    change -R' < (C (z, m v)).1 ∧ (C (z, m v)).1 < R'
    by_cases hz : z ∈ Icc (0 : ℝ) 1
    · by_cases hv : R ≤ |m v|
      · rw [htail z (m v) hv]
        exact ⟨hvlo, hvhi⟩
      · have hvR : m v ∈ Icc (-R) R := (abs_le.mp (le_of_lt (lt_of_not_ge hv)))
        have hnorm := hB (C (z, m v)) ⟨(z, m v), ⟨hz, hvR⟩, rfl⟩
        have habs : |(C (z, m v)).1| < R' := by
          have hfst := norm_fst_le (C (z, m v))
          rw [Real.norm_eq_abs] at hfst
          exact hfst.trans_lt (hnorm.trans hBR)
        exact abs_lt.mp habs
    · have hz' : z ≤ 0 ∨ 1 ≤ z := by
        simp only [mem_Icc, not_and_or, not_le] at hz
        exact hz.imp le_of_lt le_of_lt
      rw [hstat z hz' (m v)]
      exact ⟨hvlo, hvhi⟩

theorem exists_fixedTail_openLine_inscribed_polygon
    (C : ℝ × ℝ → ℝ × ℝ) {R : ℝ} (hR : 0 < R)
    (hC : ContDiff ℝ ∞ C)
    (hinj : ∀ z, Injective (fun u : ℝ => C (z, u)))
    (hreg : ∀ z u : ℝ, fderiv ℝ (fun v : ℝ => C (z, v)) u 1 ≠ 0)
    (htail : ∀ z u, R ≤ |u| → C (z, u) = (u, 0))
    (hstat : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ u, C (z, u) = (u, 0)) :
    ∃ n : ℕ, ∃ R' : ℝ, R < R' ∧ ∃ m : Fin (n + 3) → ℝ,
      StrictMono m ∧ m 0 = -R' ∧ m (Fin.last (n + 2)) = R' ∧
      ∃ P : ℝ → Polygon (ℝ × ℝ) (n + 3),
        (∀ z v, P z v = C (z, m v)) ∧
        ∀ z, IsSimplePolygonalArc (P z) ∧ P z 0 = ((-R', 0) : ℝ × ℝ) ∧
          P z (Fin.last (n + 2)) = ((R', 0) : ℝ × ℝ) ∧
          ∀ v, v ≠ 0 → v ≠ Fin.last (n + 2) →
            LinearMap.fst ℝ ℝ ℝ ((-R', 0) : ℝ × ℝ) <
              LinearMap.fst ℝ ℝ ℝ (P z v) ∧
            LinearMap.fst ℝ ℝ ℝ (P z v) <
              LinearMap.fst ℝ ℝ ℝ ((R', 0) : ℝ × ℝ) := by
  obtain ⟨n, R', hRR, m, hm, hm0, hmN, _, _, P, hP, hgood⟩ :=
    exists_fixedTail_openLine_inscribed_polygon_fine C hR (by norm_num : (0 : ℝ) < 1)
      hC hinj hreg htail hstat
  exact ⟨n, R', hRR, m, hm, hm0, hmN, P, hP, hgood⟩

end PoincareConjecture.M25.Topology3D
