import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarMarkedCutCharts
import PoincareConjecture.Proofs.M76.Triangulation.ConvexFrontierCoordinateQuadrants

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

private theorem nonpos_iff_of_zero_nonneg {a b : ℝ}
    (hz : a = 0 ↔ b = 0) (hp : 0 ≤ a ↔ 0 ≤ b) : a ≤ 0 ↔ b ≤ 0 := by
  constructor
  · intro ha
    by_contra hb
    have hbpos : 0 < b := lt_of_not_ge hb
    have ha0 : a = 0 := le_antisymm ha (hp.mpr hbpos.le)
    exact hbpos.ne' (hz.mp ha0)
  · intro hb
    by_contra ha
    have hapos : 0 < a := lt_of_not_ge ha
    have hb0 : b = 0 := le_antisymm hb (hp.mp hapos.le)
    exact hapos.ne' (hz.mpr hb0)

theorem isFinitePLBallPair_closedStar_coordinate_caps
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    (hz : (0 : (ℝ × ℝ) × ℝ) ∈ K.vertices)
    (hint : (0 : (ℝ × ℝ) × ℝ) ∈ interior K.space)
    (c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ)) :
    (∀ j : Bool, IsFinitePLBallPair (ℝ × ℝ)
      ((K.link 0).space ∩ {x | if j then x.2 ≤ 0 else 0 ≤ x.2})
      ((K.link 0).space ∩ {x | x.2 = 0})) ∧
    ∀ i j : Bool, IsFinitePLBallPair (ℝ × ℝ)
      ((K.link 0).space ∩ {x | (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1) ∧
        (if j then x.2 ≤ 0 else 0 ≤ x.2)})
      (((K.link 0).space ∩ {x | x.1.1 = 0 ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)}) ∪
        ((K.link 0).space ∩ {x | x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1)})) := by
  classical
  let A : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let B : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let F : Bool → ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℝ := fun j => if j then B else A
  obtain ⟨C, _, H, hC, hcv, hC0, _, _, hH, hboundary, hmarks⟩ :=
    K.exists_finitePL_closedStar_chart_preserving_cut_family hK hz hint c F
  obtain ⟨g, ⟨J, hJ, hJC, hg⟩, hginv⟩ := hH.symm
  have hgfull : FinitePiecewiseAffineOn g C := ⟨J, hJ, hJC, hg⟩
  have hgin (x : (ℝ × ℝ) × ℝ) (hx : x ∈ C) : g x ∈ (K.closedStar 0).space := by
    rw [← hginv ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hforward (x : (ℝ × ℝ) × ℝ) (hx : x ∈ C) :
      (H ⟨g x, hgin x hx⟩ : (ℝ × ℝ) × ℝ) = x := by
    have he : (⟨g x, hgin x hx⟩ : (K.closedStar 0).space) = H.symm ⟨x, hx⟩ :=
      Subtype.ext (hginv ⟨x, hx⟩).symm
    rw [he, H.apply_symm_apply]
  have hback (x : (K.closedStar 0).space) : g (H x) = x := by
    rw [← hginv (H x), H.symm_apply_apply]
  have hginj : InjOn g C := by
    intro x hx y hy hxy
    have he : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hginv] using hxy
    exact congrArg Subtype.val (H.symm.injective he)
  have hX (x : (ℝ × ℝ) × ℝ) (hx : x ∈ C) :
      (x.1.1 = 0 ↔ (g x).1.1 = 0) ∧ (0 ≤ x.1.1 ↔ 0 ≤ (g x).1.1) := by
    have h := hmarks false ⟨g x, hgin x hx⟩
    change ((H ⟨g x, hgin x hx⟩ : (ℝ × ℝ) × ℝ).1.1 = 0 ↔ (g x).1.1 = 0) ∧
      (0 ≤ (H ⟨g x, hgin x hx⟩ : (ℝ × ℝ) × ℝ).1.1 ↔ 0 ≤ (g x).1.1) at h
    rwa [hforward x hx] at h
  have hZ (x : (ℝ × ℝ) × ℝ) (hx : x ∈ C) :
      (x.2 = 0 ↔ (g x).2 = 0) ∧ (0 ≤ x.2 ↔ 0 ≤ (g x).2) := by
    have h := hmarks true ⟨g x, hgin x hx⟩
    change ((H ⟨g x, hgin x hx⟩ : (ℝ × ℝ) × ℝ).2 = 0 ↔ (g x).2 = 0) ∧
      (0 ≤ (H ⟨g x, hgin x hx⟩ : (ℝ × ℝ) × ℝ).2 ↔ 0 ≤ (g x).2) at h
    rwa [hforward x hx] at h
  have hXs (i : Bool) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ C) :
      (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1) ↔
        (if i then (g x).1.1 ≤ 0 else 0 ≤ (g x).1.1) := by
    cases i
    · exact (hX x hx).2
    · exact nonpos_iff_of_zero_nonneg (hX x hx).1 (hX x hx).2
  have hZs (j : Bool) (x : (ℝ × ℝ) × ℝ) (hx : x ∈ C) :
      (if j then x.2 ≤ 0 else 0 ≤ x.2) ↔
        (if j then (g x).2 ≤ 0 else 0 ≤ (g x).2) := by
    cases j
    · exact (hZ x hx).2
    · exact nonpos_iff_of_zero_nonneg (hZ x hx).1 (hZ x hx).2
  have hlinksub : (K.link 0).space ⊆ (K.closedStar 0).space :=
    space_subset_of_le (K.link_le_closedStar 0)
  have himage (P : ((ℝ × ℝ) × ℝ) → Prop)
      (hP : ∀ x ∈ C, P x ↔ P (g x)) :
      g '' (frontier C ∩ {x | P x}) = (K.link 0).space ∩ {x | P x} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxC := hC.isClosed.frontier_subset hx.1
      refine ⟨(hboundary ⟨g x, hgin x hxC⟩).mpr ?_, (hP x hxC).mp hx.2⟩
      rw [hforward x hxC]
      exact hx.1
    · intro hy
      let z : (K.closedStar 0).space := ⟨y, hlinksub hy.1⟩
      refine ⟨H z, ⟨(hboundary z).mp hy.1, ?_⟩, hback z⟩
      apply (hP (H z) (H z).property).mpr
      rw [hback z]
      exact hy.2
  have hpull (P Q : ((ℝ × ℝ) × ℝ) → Prop)
      (hP : ∀ x ∈ C, P x ↔ P (g x)) (hQ : ∀ x ∈ C, Q x ↔ Q (g x))
      (hb : IsFinitePLBallPair (ℝ × ℝ)
        (frontier C ∩ {x | P x}) (frontier C ∩ {x | Q x})) :
      IsFinitePLBallPair (ℝ × ℝ)
        ((K.link 0).space ∩ {x | P x}) ((K.link 0).space ∩ {x | Q x}) := by
    have hr := hb.image_of_subset hgfull
      (show frontier C ∩ {x | P x} ⊆ C from
        fun _ hx => hC.isClosed.frontier_subset hx.1) hginj
    simpa only [himage P hP, himage Q hQ] using hr
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) =
      Module.finrank ℝ (ℝ × ℝ) + 1 := by simp [Module.finrank_prod]
  obtain ⟨_, qn, _, hqn, _, _, _, hqnB⟩ :=
    hC.exists_frontier_and_interior_linear_sign hcv hC0 A (-B)
      (v := ((0, 0), -1)) rfl (by norm_num [B])
  obtain ⟨_, qp, _, hqp, _, _, _, hqpB⟩ :=
    hC.exists_frontier_and_interior_linear_sign hcv hC0 A B
      (v := ((0, 0), 1)) rfl (by norm_num [B])
  have hcap (j : Bool) : IsFinitePLBallPair (ℝ × ℝ)
      (frontier C ∩ {x | if j then x.2 ≤ 0 else 0 ≤ x.2})
      (frontier C ∩ {x | x.2 = 0}) := by
    cases j
    · exact J.isFinitePLBallPair_convex_frontier_affine_cap hJ hC hcv hJC
        B.toAffineMap ⟨qn, hqn, neg_pos.mp hqnB⟩ ⟨0, hC0, B.map_zero⟩ hdim
    · have h := J.isFinitePLBallPair_convex_frontier_affine_cap hJ hC hcv hJC
        (-B).toAffineMap (F := ℝ × ℝ) ⟨qp, hqp, neg_neg_of_pos hqpB⟩
        ⟨0, hC0, (-B).map_zero⟩ hdim
      simpa only [LinearMap.coe_toAffineMap, LinearMap.neg_apply, neg_nonneg,
        neg_eq_zero, B, LinearMap.snd_apply, ite_true] using h
  obtain ⟨hn, hnC⟩ := hC.gauge_inv_smul_mem_frontier hcv hC0
    (show (((0, -1), 0) : (ℝ × ℝ) × ℝ) ≠ 0 by norm_num)
  obtain ⟨hp, hpC⟩ := hC.gauge_inv_smul_mem_frontier hcv hC0
    (show (((0, 1), 0) : (ℝ × ℝ) × ℝ) ≠ 0 by norm_num)
  let a := -(gauge C (((0, -1), 0) : (ℝ × ℝ) × ℝ))⁻¹
  let b := (gauge C (((0, 1), 0) : (ℝ × ℝ) × ℝ))⁻¹
  have ha : a < 0 := neg_neg_of_pos hn
  have hb : 0 < b := hp
  have haC : ((0, a), 0) ∈ frontier C := by simpa [a, smul_eq_mul] using hnC
  have hbC : ((0, b), 0) ∈ frontier C := by simpa [b, smul_eq_mul] using hpC
  obtain ⟨_, _, hquad⟩ := J.isFinitePLBallPair_coordinate_frontier_quadrants
    hJ hC hcv hJC hC0 ha hb haC hbC
  refine ⟨?_, ?_⟩
  · intro j
    exact hpull _ _ (hZs j) (fun x hx => (hZ x hx).1) (hcap j)
  · intro i j
    let P : ((ℝ × ℝ) × ℝ) → Prop := fun x =>
      (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1) ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)
    let Q : ((ℝ × ℝ) × ℝ) → Prop := fun x =>
      (x.1.1 = 0 ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)) ∨
        (x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1))
    have hrim (S : Set ((ℝ × ℝ) × ℝ)) :
        (S ∩ {x | x.1.1 = 0 ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)}) ∪
          (S ∩ {x | x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1)}) =
          S ∩ {x | Q x} := by
      ext x
      simp only [mem_union, mem_inter_iff, mem_ofPred_eq, Q]
      tauto
    have hq := hquad i j
    rw [hrim] at hq
    rw [hrim]
    exact hpull P Q (fun x hx => (hXs i x hx).and (hZs j x hx))
      (fun x hx => ((hX x hx).1.and (hZs j x hx)).or
        ((hZ x hx).1.and (hXs i x hx))) hq

end Geometry.SimplicialComplex
