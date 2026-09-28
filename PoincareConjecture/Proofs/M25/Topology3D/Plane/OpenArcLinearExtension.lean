import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcParameter
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedVertexPath
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OppositeCoordinate

set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem roundedVertexPath_abs_eq_edge {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : ℤ → E)
    (i : ℤ) {t : ℝ} (ht : t ∈ Icc (i : ℝ) ((i : ℝ) + 1)) :
    roundedVertexPath abs P t = AffineMap.lineMap (P i) (P (i + 1)) (t - i) := by
  by_cases hleft : t < (i : ℝ) + 1 / 2
  · have hfloor : ⌊t + 1 / 2⌋ = i := Int.floor_eq_iff.mpr (by
      constructor <;> linarith [ht.1])
    rw [roundedVertexPath, hfloor, roundedCorner,
      abs_of_nonneg (sub_nonneg.mpr ht.1), AffineMap.lineMap_apply_module']
    module
  · have hfloor : ⌊t + 1 / 2⌋ = i + 1 := Int.floor_eq_iff.mpr (by
      simp only [Int.cast_add, Int.cast_one]
      constructor <;> linarith [ht.2])
    rw [roundedVertexPath, hfloor, roundedCorner]
    simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
    rw [abs_of_nonpos (by linarith [ht.2]), AffineMap.lineMap_apply_module']
    module

private theorem roundedVertexPath_abs_int {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : ℤ → E) (i : ℤ) :
    roundedVertexPath abs P (i : ℝ) = P i := by
  rw [roundedVertexPath_abs_eq_edge P i ⟨le_rfl, by linarith⟩]
  simp only [sub_self, AffineMap.lineMap_apply_zero]

private theorem continuous_roundedVertexPath_abs {Z : Type*}
    [TopologicalSpace Z] {P : Z → ℤ → ℝ × ℝ}
    (hP : ∀ i, Continuous (fun z => P z i)) :
    Continuous (fun x : Z × ℝ => roundedVertexPath abs (P x.1) x.2) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let i : ℤ := ⌊x.2 + 1 / 2⌋
  have hlo : (i : ℝ) ≤ x.2 + 1 / 2 := Int.floor_le _
  have hhi : x.2 + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have hx : x.2 ∈ Ioo ((i : ℝ) - 1 + 1 / 4) ((i : ℝ) + 1 - 1 / 4) := by
    constructor <;> linarith
  have hF : Continuous (fun y : Z × ℝ => roundedCorner abs
      (P y.1 i) (P y.1 i - P y.1 (i - 1))
      (P y.1 (i + 1) - P y.1 i) (y.2 - i)) := by
    have hi : Continuous (fun y : Z × ℝ => P y.1 i) := (hP i).comp continuous_fst
    have hm : Continuous (fun y : Z × ℝ => P y.1 (i - 1)) :=
      (hP (i - 1)).comp continuous_fst
    have hn : Continuous (fun y : Z × ℝ => P y.1 (i + 1)) :=
      (hP (i + 1)).comp continuous_fst
    have ht : Continuous (fun y : Z × ℝ => y.2 - (i : ℝ)) :=
      continuous_snd.sub continuous_const
    exact (hi.add (((ht.sub ht.abs).div_const 2).smul (hi.sub hm))).add
      (((ht.add ht.abs).div_const 2).smul (hn.sub hi))
  apply hF.continuousAt.congr_of_eventuallyEq
  have hU : ∀ᶠ y : Z × ℝ in 𝓝 x,
      y.2 ∈ Ioo ((i : ℝ) - 1 + 1 / 4) ((i : ℝ) + 1 - 1 / 4) :=
    continuous_snd.continuousAt (isOpen_Ioo.mem_nhds hx)
  filter_upwards [hU] with y hy
  exact roundedVertexPath_eq_local (P y.1) (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num) (fun _ _ => rfl) (fun s => ⟨le_rfl, by linarith⟩) i hy

variable {n : ℕ}

noncomputable def openArcExtendedVertex (p : Polygon (ℝ × ℝ) (n + 2))
    (j : ℤ) : ℝ × ℝ :=
  if 0 ≤ j ∧ j ≤ (n + 1 : ℕ) then p (polygonIntegerIndex (n + 2) j)
  else ((j : ℝ), 0)

noncomputable def openArcLinearParameter (p : Polygon (ℝ × ℝ) (n + 2)) : ℝ → ℝ × ℝ :=
  roundedVertexPath abs (openArcExtendedVertex p)

theorem openArcExtendedVertex_nat (p : Polygon (ℝ × ℝ) (n + 2))
    (i : Fin (n + 2)) : openArcExtendedVertex p (i.val : ℤ) = p i := by
  have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ (n + 1 : ℕ) := by
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast (show i.val ≤ n + 1 by omega)
  simp only [openArcExtendedVertex, if_pos hi, polygonIntegerIndex_nat]

theorem openArcExtendedVertex_of_nonpos (p : Polygon (ℝ × ℝ) (n + 2))
    (h0 : p 0 = (0, 0)) {j : ℤ} (hj : j ≤ 0) :
    openArcExtendedVertex p j = ((j : ℝ), 0) := by
  by_cases hj0 : j = 0
  · subst j
    simpa only [Fin.val_zero, Nat.cast_zero, Int.cast_zero, h0] using
      openArcExtendedVertex_nat p 0
  · have hnot : ¬ (0 ≤ j ∧ j ≤ (n + 1 : ℕ)) := by omega
    exact if_neg hnot

theorem openArcExtendedVertex_of_ge (p : Polygon (ℝ × ℝ) (n + 2))
    (hN : p (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0))
    {j : ℤ} (hj : (n + 1 : ℕ) ≤ j) :
    openArcExtendedVertex p j = ((j : ℝ), 0) := by
  by_cases hjN : j = (n + 1 : ℕ)
  · subst j
    simpa only [Fin.val_last, Int.cast_natCast, hN] using
      openArcExtendedVertex_nat p (Fin.last (n + 1))
  · have hnot : ¬ (0 ≤ j ∧ j ≤ (n + 1 : ℕ)) := by omega
    exact if_neg hnot

theorem contDiff_openArcExtendedVertex {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {p : V → Polygon (ℝ × ℝ) (n + 2)}
    (hp : ∀ i, ContDiff ℝ ∞ (fun z => p z i)) (j : ℤ) :
    ContDiff ℝ ∞ (fun z => openArcExtendedVertex (p z) j) := by
  by_cases hj : 0 ≤ j ∧ j ≤ (n + 1 : ℕ)
  · simpa only [openArcExtendedVertex, if_pos hj] using hp (polygonIntegerIndex (n + 2) j)
  · simpa only [openArcExtendedVertex, if_neg hj] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : V => ((j : ℝ), (0 : ℝ))))

theorem continuous_openArcLinearParameter {Z : Type*} [TopologicalSpace Z]
    {p : Z → Polygon (ℝ × ℝ) (n + 2)} (hp : ∀ i, Continuous (fun z => p z i)) :
    Continuous (fun x : Z × ℝ => openArcLinearParameter (p x.1) x.2) := by
  change Continuous (fun x : Z × ℝ => roundedVertexPath abs (openArcExtendedVertex (p x.1)) x.2)
  apply continuous_roundedVertexPath_abs (P := fun z => openArcExtendedVertex (p z))
  intro j
  by_cases hj : 0 ≤ j ∧ j ≤ (n + 1 : ℕ)
  · simpa only [openArcExtendedVertex, if_pos hj] using hp (polygonIntegerIndex (n + 2) j)
  · simpa only [openArcExtendedVertex, if_neg hj] using
      (continuous_const : Continuous (fun _ : Z => ((j : ℝ), (0 : ℝ))))

private theorem exists_openArc_edge {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
    ∃ i : Fin (n + 1), u ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1) := by
  by_cases heq : u = (n + 1 : ℕ)
  · refine ⟨Fin.last n, ?_⟩
    rw [heq]
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one, mem_Icc]
    exact ⟨by linarith, le_rfl⟩
  · let j : ℤ := ⌊u⌋
    have hj0 : 0 ≤ j := Int.floor_nonneg.mpr hu.1
    have hjn : j < (n + 1 : ℕ) := by
      exact_mod_cast (Int.floor_le u).trans_lt (lt_of_le_of_ne hu.2 heq)
    let i : Fin (n + 1) := ⟨j.toNat, (Int.toNat_lt hj0).mpr hjn⟩
    have hval : (i.val : ℝ) = (j : ℝ) := by
      dsimp only [i]
      exact_mod_cast Int.toNat_of_nonneg hj0
    refine ⟨i, ?_⟩
    rw [hval]
    exact ⟨Int.floor_le u, (Int.lt_floor_add_one u).le⟩

theorem openArcLinearParameter_eq_polygon (p : Polygon (ℝ × ℝ) (n + 2))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
    openArcLinearParameter p u = polygonLinearParameter p u := by
  obtain ⟨i, hi⟩ := exists_openArc_edge hu
  have hi' : u ∈ Icc ((i.val : ℤ) : ℝ) (((i.val : ℤ) : ℝ) + 1) := by
    simpa only [Int.cast_natCast] using hi
  have hleft : openArcExtendedVertex p (i.val : ℤ) = p i.castSucc :=
    openArcExtendedVertex_nat p i.castSucc
  have hright : openArcExtendedVertex p ((i.val : ℤ) + 1) = p i.succ := by
    simpa only [Fin.val_succ, Int.natCast_add, Int.natCast_one] using
      openArcExtendedVertex_nat p i.succ
  have hindex : polygonIntegerIndex (n + 2) (i.val : ℤ) = i.castSucc :=
    polygonIntegerIndex_nat i.castSucc
  rw [openArcLinearParameter, roundedVertexPath_abs_eq_edge _ _ hi', hleft, hright,
    polygonLinearParameter_eq_edge p (i.val : ℤ) hi', hindex]
  have hnext : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [Polygon.edgePath, hnext]

theorem openArcLinearParameter_of_nonpos (p : Polygon (ℝ × ℝ) (n + 2))
    (h0 : p 0 = (0, 0)) {u : ℝ} (hu : u ≤ 0) :
    openArcLinearParameter p u = (u, 0) := by
  by_cases hu0 : u = 0
  · subst u
    have heq : openArcLinearParameter p 0 = openArcExtendedVertex p 0 := by
      simpa only [openArcLinearParameter, Int.cast_zero] using
        roundedVertexPath_abs_int (openArcExtendedVertex p) 0
    exact heq.trans (by simpa only [Int.cast_zero] using
      openArcExtendedVertex_of_nonpos p h0 (j := 0) le_rfl)
  · let j : ℤ := ⌊u⌋
    have hj : j < 0 := by
      exact_mod_cast (Int.floor_le u).trans_lt (lt_of_le_of_ne hu hu0)
    rw [openArcLinearParameter, roundedVertexPath_abs_eq_edge _ j
      ⟨Int.floor_le u, (Int.lt_floor_add_one u).le⟩,
      openArcExtendedVertex_of_nonpos p h0 hj.le,
      openArcExtendedVertex_of_nonpos p h0 (show j + 1 ≤ 0 by omega),
      AffineMap.lineMap_apply_module']
    simp only [Int.cast_add, Int.cast_one]
    ext <;> dsimp <;> ring

theorem openArcLinearParameter_of_ge (p : Polygon (ℝ × ℝ) (n + 2))
    (hN : p (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0))
    {u : ℝ} (hu : (n + 1 : ℕ) ≤ u) : openArcLinearParameter p u = (u, 0) := by
  let j : ℤ := ⌊u⌋
  have hj : (n + 1 : ℕ) ≤ j := Int.le_floor.mpr (by simpa only [Int.cast_natCast] using hu)
  rw [openArcLinearParameter, roundedVertexPath_abs_eq_edge _ j
    ⟨Int.floor_le u, (Int.lt_floor_add_one u).le⟩,
    openArcExtendedVertex_of_ge p hN hj,
    openArcExtendedVertex_of_ge p hN (show (n + 1 : ℕ) ≤ j + 1 by omega),
    AffineMap.lineMap_apply_module']
  simp only [Int.cast_add, Int.cast_one]
  ext <;> dsimp <;> ring

private theorem openArcLinearParameter_fst_bounds (p : Polygon (ℝ × ℝ) (n + 2))
    (hp : ∀ k, (p k).1 ∈ Icc (0 : ℝ) (n + 1 : ℕ))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
    (openArcLinearParameter p u).1 ∈ Icc (0 : ℝ) (n + 1 : ℕ) := by
  rw [openArcLinearParameter_eq_polygon p hu]
  have hmem : polygonLinearParameter p u ∈ polygonArcBoundary p := by
    rw [← image_polygonLinearParameter_arc p]
    exact mem_image_of_mem _ hu
  obtain ⟨i, t, ht, heq⟩ := mem_iUnion.mp hmem
  change p.edgePath ℝ i.castSucc t = polygonLinearParameter p u at heq
  rw [← heq]
  change (AffineMap.lineMap (p i.castSucc) (p (finRotate (n + 2) i.castSucc)) t).1 ∈ _
  have hnext : finRotate (n + 2) i.castSucc = i.succ := finRotate_of_lt i.isLt
  rw [hnext]
  have h := (convex_Icc (0 : ℝ) (n + 1 : ℕ)).lineMap_mem (hp i.castSucc) (hp i.succ) ht
  simpa only [AffineMap.lineMap_apply_module, Prod.fst_add, Prod.smul_fst] using h

theorem openArcLinearParameter_injective (p : Polygon (ℝ × ℝ) (n + 2))
    (hp : IsSimplePolygonalArc p) (h0 : p 0 = (0, 0))
    (hN : p (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0))
    (hstrip : ∀ k, (p k).1 ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
    Injective (openArcLinearParameter p) := by
  have hout (u : ℝ) (hu : u ∉ Icc (0 : ℝ) (n + 1 : ℕ)) :
      openArcLinearParameter p u = (u, 0) := by
    by_cases hle : u ≤ 0
    · exact openArcLinearParameter_of_nonpos p h0 hle
    · apply openArcLinearParameter_of_ge p hN
      by_contra hn
      exact hu ⟨(lt_of_not_ge hle).le, (lt_of_not_ge hn).le⟩
  have hno (u v : ℝ) (hu : u ∉ Icc (0 : ℝ) (n + 1 : ℕ))
      (hv : v ∈ Icc (0 : ℝ) (n + 1 : ℕ)) :
      openArcLinearParameter p u ≠ openArcLinearParameter p v := by
    intro heq
    have hb := openArcLinearParameter_fst_bounds p hstrip hv
    have he := congrArg Prod.fst heq
    rw [hout u hu] at he
    change u = (openArcLinearParameter p v).1 at he
    rw [← he] at hb
    exact hu hb
  intro s t heq
  by_cases hs : s ∈ Icc (0 : ℝ) (n + 1 : ℕ)
  · by_cases ht : t ∈ Icc (0 : ℝ) (n + 1 : ℕ)
    · rw [openArcLinearParameter_eq_polygon p hs, openArcLinearParameter_eq_polygon p ht] at heq
      exact hp.injOn_polygonLinearParameter hs ht heq
    · exact (hno t s ht hs heq.symm).elim
  · by_cases ht : t ∈ Icc (0 : ℝ) (n + 1 : ℕ)
    · exact (hno s t hs ht heq).elim
    · rw [hout s hs, hout t ht] at heq
      exact congrArg Prod.fst heq

theorem exists_positive_corner_functional_of_injective_vertexPath
    (P : ℤ → ℝ × ℝ) (hP : Injective (roundedVertexPath abs P)) (i : ℤ) :
    ∃ ℓ : (ℝ × ℝ) →L[ℝ] ℝ,
      0 < ℓ (P i - P (i - 1)) ∧ 0 < ℓ (P (i + 1) - P i) := by
  have hvertex : ∀ j : ℤ, roundedVertexPath abs P (j : ℝ) = P j :=
    roundedVertexPath_abs_int P
  have ha : P (i - 1) ≠ P i := by
    intro heq
    have h := hP ((hvertex (i - 1)).trans (heq.trans (hvertex i).symm))
    simp only [Int.cast_sub, Int.cast_one] at h
    linarith
  have hb : P (i + 1) ≠ P i := by
    intro heq
    have h := hP ((hvertex (i + 1)).trans (heq.trans (hvertex i).symm))
    simp only [Int.cast_add, Int.cast_one] at h
    linarith
  have hinter : segment ℝ (P i) (P (i - 1)) ∩ segment ℝ (P i) (P (i + 1)) ⊆ {P i} := by
    intro x hx
    rw [segment_eq_image_lineMap, segment_eq_image_lineMap] at hx
    obtain ⟨a, haI, hax⟩ := hx.1
    obtain ⟨b, hbI, hbx⟩ := hx.2
    have hleft : roundedVertexPath abs P ((i : ℝ) - a) =
        AffineMap.lineMap (P i) (P (i - 1)) a := by
      rw [roundedVertexPath_abs_eq_edge P (i - 1) (by
        simp only [Int.cast_sub, Int.cast_one, mem_Icc]
        constructor <;> linarith [haI.1, haI.2])]
      simp only [sub_add_cancel, Int.cast_sub, Int.cast_one, AffineMap.lineMap_apply_module']
      module
    have hright : roundedVertexPath abs P ((i : ℝ) + b) =
        AffineMap.lineMap (P i) (P (i + 1)) b := by
      rw [roundedVertexPath_abs_eq_edge P i (by constructor <;> linarith [hbI.1, hbI.2])]
      congr 1
      ring
    have heq := hP ((hleft.trans hax).trans (hright.trans hbx).symm)
    have ha0 : a = 0 := by linarith [haI.1, hbI.1]
    rw [ha0, AffineMap.lineMap_apply_zero] at hax
    exact hax.symm
  obtain ⟨X, hneg, hpos⟩ := exists_linearMap_neg_pos_of_not_sameRay
    (not_sameRay_sub_of_segments_inter_subset_singleton ha hb hinter)
  refine ⟨X.toContinuousLinearMap, ?_, hpos⟩
  change 0 < X (P i - P (i - 1))
  have heq : X (P i - P (i - 1)) = -X (P (i - 1) - P i) := by
    simp only [map_sub]
    ring
  rw [heq]
  exact neg_pos.mpr hneg

theorem openArcExtendedVertex_secondDiff_zero (p : Polygon (ℝ × ℝ) (n + 2))
    (h0 : p 0 = (0, 0)) (hN : p (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0))
    {j : ℤ} (hj : j < 0 ∨ (n + 1 : ℕ) < j) :
    (openArcExtendedVertex p (j + 1) - openArcExtendedVertex p j) -
      (openArcExtendedVertex p j - openArcExtendedVertex p (j - 1)) = 0 := by
  rcases hj with hj | hj
  · rw [openArcExtendedVertex_of_nonpos p h0 (show j + 1 ≤ 0 by omega),
      openArcExtendedVertex_of_nonpos p h0 hj.le,
      openArcExtendedVertex_of_nonpos p h0 (show j - 1 ≤ 0 by omega)]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_one]
    ext <;> dsimp <;> ring
  · rw [openArcExtendedVertex_of_ge p hN (show (n + 1 : ℕ) ≤ j + 1 by omega),
      openArcExtendedVertex_of_ge p hN hj.le,
      openArcExtendedVertex_of_ge p hN (show (n + 1 : ℕ) ≤ j - 1 by omega)]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_one]
    ext <;> dsimp <;> ring

end PoincareConjecture.M25.Topology3D
