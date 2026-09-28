import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSimplexCylinder
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

noncomputable def handleCoordinateSplit (J : Finset (Fin 3)) :
    (Fin 3 → ℝ) ≃L[ℝ] ((J → ℝ) × ({i : Fin 3 // i ∉ J} → ℝ)) := by
  classical
  let e : (Fin 3 → ℝ) ≃ₗ[ℝ] ((J → ℝ) × ({i : Fin 3 // i ∉ J} → ℝ)) := {
    toFun := fun x => (fun i => x i, fun i => x i)
    invFun := fun z i => if hi : i ∈ J then z.1 ⟨i, hi⟩ else z.2 ⟨i, hi⟩
    left_inv := by intro x; funext i; dsimp only; split <;> rfl
    right_inv := by
      intro z
      apply Prod.ext
      · funext i
        simp only [dif_pos i.property]
      · funext i
        simp only [dif_neg i.property]
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  exact e.toContinuousLinearEquiv

theorem norm_handleCoordinateSplit (J : Finset (Fin 3)) (x : Fin 3 → ℝ) :
    ‖handleCoordinateSplit J x‖ = ‖x‖ := by
  classical
  let e := handleCoordinateSplit J
  have ht : ‖(e x).1‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    exact norm_le_pi_norm x i
  have hn : ‖(e x).2‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    exact norm_le_pi_norm x i
  change ‖e x‖ = ‖x‖
  rw [Prod.norm_def]
  apply le_antisymm (max_le ht hn)
  apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr
  intro i
  by_cases hi : i ∈ J
  · exact (norm_le_pi_norm (e x).1 ⟨i, hi⟩).trans (le_max_left _ _)
  · exact (norm_le_pi_norm (e x).2 ⟨i, hi⟩).trans (le_max_right _ _)

theorem exists_open_simplex_cylinder
    (J : Finset (Fin 3)) {D : Set (J → ℝ)}
    (h : closedBall (0 : J → ℝ) 1 ≃ₜ D) (hh : h.IsFinitePL)
    (Phi : ((J → ℝ) × ({i : Fin 3 // i ∉ J} → ℝ)) ≃ᴬ[ℝ] (Fin 3 → ℝ))
    {U V P : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hV : IsOpen V) (hP : IsClosed P)
    (hDV : ∀ x ∈ D, Phi (x, 0) ∈ V)
    (hDP : ∀ x ∈ interior D, Phi (x, 0) ∉ P)
    (hfront : ∀ x : closedBall (0 : J → ℝ) 1,
      ‖(x : J → ℝ)‖ = 1 → Phi ((h x : J → ℝ), 0) ∈ U) :
    ∃ (p : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ))
      (N : Set (Fin 3 → ℝ)),
      coordinateCylinder J ⊆ p.source ∧
      LocallyPiecewiseAffineOn p p.source ∧
      LocallyPiecewiseAffineOn p.symm p.target ∧
      p.target ⊆ V \ P ∧ IsOpen N ∧
      N = p.source ∩ p ⁻¹' U ∧ frontier (coordinateCylinder J) ⊆ N ∧
      Phi '' (D ×ˢ ({0} : Set ({i : Fin 3 // i ∉ J} → ℝ))) ⊆
        (U \ (p '' (coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2))) ∪
          p '' (ball (0 : Fin 3 → ℝ) 1 ∪ (N ∩ handleTransverseStrip J)) := by
  classical
  let T := J → ℝ
  let Z := {i : Fin 3 // i ∉ J} → ℝ
  let split := handleCoordinateSplit J
  obtain ⟨H, a, b, delta, hHs, _hHt, hH, _hHi, hHval, hab, hb1, hd,
      hleftover, hwidthV, hwidthU⟩ :=
    exists_cubical_collar_width h hh Phi hU hV hP hDV hDP hfront
  have ha : 0 < a := hab.1
  have ha1 : a < 1 := hab.2.trans hb1
  let sa : T ≃ᴬ[ℝ] T :=
    (LinearEquiv.smulOfNeZero ℝ T a ha.ne').toContinuousLinearEquiv.toContinuousAffineEquiv
  let sd : Z ≃ᴬ[ℝ] Z :=
    (LinearEquiv.smulOfNeZero ℝ Z delta hd.ne').toContinuousLinearEquiv.toContinuousAffineEquiv
  let Hb := H.restrOpen (ball (0 : T) b) isOpen_ball
  let q := sa.toHomeomorph.transOpenPartialHomeomorph Hb
  obtain ⟨c, hcs, hct, hcfix, hc, _hci⟩ := exists_plCubeCompression {i : Fin 3 // i ∉ J}
  let cd := c.trans sd.toHomeomorph.toOpenPartialHomeomorph
  let R := (q.prod cd).trans Phi.toHomeomorph.toOpenPartialHomeomorph
  let p := split.toHomeomorph.transOpenPartialHomeomorph R
  have hpFormula (x : Fin 3 → ℝ) :
      p x = Phi (H (a • (split x).1), delta • c (split x).2) := rfl
  have hsource (x : Fin 3 → ℝ) : x ∈ p.source ↔ a • (split x).1 ∈ ball (0 : T) b := by
    change ((sa (split x).1 ∈ H.source ∧ sa (split x).1 ∈ ball (0 : T) b) ∧
      (split x).2 ∈ c.source ∧ sd (c (split x).2) ∈ univ) ∧
      Phi (q (split x).1, cd (split x).2) ∈ univ ↔ _
    rw [hcs]
    simp only [mem_univ, and_true]
    constructor
    · exact fun hx => hx.2
    · intro hx
      refine ⟨?_, hx⟩
      rw [hHs, mem_ball_zero_iff]
      exact (mem_ball_zero_iff.mp hx).trans hb1
  have htan (x : Fin 3 → ℝ) (hx : x ∈ coordinateCylinder J) : ‖(split x).1‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    change ‖x i‖ ≤ 1
    simpa only [Real.norm_eq_abs] using hx i i.property
  have hscaled (x : Fin 3 → ℝ) (hx : x ∈ coordinateCylinder J) :
      ‖a • (split x).1‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_of_le_one_right ha.le (htan x hx)
  have hpSource : coordinateCylinder J ⊆ p.source := by
    intro x hx
    apply (hsource x).mpr
    rw [mem_ball_zero_iff]
    exact (hscaled x hx).trans_lt hab.2
  have hnormal (x : Z) : delta • c x ∈ closedBall (0 : Z) (2 * delta) := by
    have hx : x ∈ c.source := hcs.symm ▸ mem_univ x
    have hcNorm : ‖c x‖ < 2 := mem_ball_zero_iff.mp (hct ▸ c.map_source hx)
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  have htarget : p.target ⊆ V \ P := by
    intro y hy
    have hx := p.map_target hy
    have hxb := (hsource (p.symm y)).mp hx
    rw [← p.right_inv hy, hpFormula]
    apply hwidthV
    exact ⟨_, ⟨⟨_, ball_subset_closedBall hxb, rfl⟩, hnormal _⟩, rfl⟩
  have hsaPL : LocallyPiecewiseAffineOn sa univ :=
    locallyPiecewiseAffineOn_affine sa.toContinuousAffineMap isOpen_univ
  have hHbPL : LocallyPiecewiseAffineOn Hb Hb.source :=
    (hH.mono Hb.open_source inter_subset_left).congr (fun _ _ => rfl)
  have hqPL : LocallyPiecewiseAffineOn q q.source := by
    exact ((hHbPL.comp hsaPL).mono q.open_source
      (fun _ hx => ⟨mem_univ _, hx⟩)).congr (fun _ _ => rfl)
  have hsdPL : LocallyPiecewiseAffineOn sd univ :=
    locallyPiecewiseAffineOn_affine sd.toContinuousAffineMap isOpen_univ
  have hcdPL : LocallyPiecewiseAffineOn cd cd.source := by
    exact ((hsdPL.comp hc).mono cd.open_source
      (fun _ hx => ⟨hx.1, mem_univ _⟩)).congr (fun _ _ => rfl)
  have hPhiPL : LocallyPiecewiseAffineOn Phi univ :=
    locallyPiecewiseAffineOn_affine Phi.toContinuousAffineMap isOpen_univ
  have hRPL : LocallyPiecewiseAffineOn R R.source := by
    exact ((hPhiPL.comp (hqPL.prodMap hcdPL)).mono R.open_source
      (fun _ hx => ⟨hx.1, mem_univ _⟩)).congr (fun _ _ => rfl)
  have hsplitPL : LocallyPiecewiseAffineOn split univ :=
    locallyPiecewiseAffineOn_affine
      split.toContinuousLinearMap.toContinuousAffineMap isOpen_univ
  have hpPL : LocallyPiecewiseAffineOn p p.source := by
    exact ((hRPL.comp hsplitPL).mono p.open_source
      (fun _ hx => ⟨mem_univ _, hx⟩)).congr (fun _ _ => rfl)
  let Nset := p.source ∩ p ⁻¹' U
  have hNopen : IsOpen Nset := p.isOpen_inter_preimage hU
  have hfrontNorm (x : Fin 3 → ℝ) (hx : x ∈ frontier (coordinateCylinder J)) :
      ‖(split x).1‖ = 1 := by
    have hxcyl : x ∈ coordinateCylinder J :=
      (isClosed_coordinateCylinder J).frontier_subset hx
    apply (htan x hxcyl).antisymm
    by_contra hn
    have hlt : ‖(split x).1‖ < 1 := lt_of_not_ge hn
    let O : Set (Fin 3 → ℝ) := {y | ‖(split y).1‖ < 1}
    have hO : IsOpen O := isOpen_lt (continuous_norm.comp
      (continuous_fst.comp split.continuous)) continuous_const
    have hOC : O ⊆ coordinateCylinder J := by
      intro y hy i hi
      have hv := (norm_le_pi_norm (split y).1 ⟨i, hi⟩).trans hy.le
      change ‖y i‖ ≤ 1 at hv
      simpa only [Real.norm_eq_abs] using hv
    exact hx.2 (hO.subset_interior_iff.mpr hOC hlt)
  have hfrontN : frontier (coordinateCylinder J) ⊆ Nset := by
    intro x hx
    have hxcyl := (isClosed_coordinateCylinder J).frontier_subset hx
    refine ⟨hpSource hxcyl, ?_⟩
    change p x ∈ U
    rw [hpFormula]
    apply hwidthU
    refine ⟨_, ⟨⟨a • (split x).1, ?_, rfl⟩, hnormal _⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, hfrontNorm x hx, mul_one]
  refine ⟨p, Nset, hpSource, hpPL, p.locallyPiecewiseAffineOn_symm hpPL,
    htarget, hNopen, rfl, hfrontN, ?_⟩
  rintro _ ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩
  have hz0 : z = 0 := mem_singleton_iff.mp hz
  subst z
  obtain ⟨v, hv⟩ := h.surjective ⟨y, hy⟩
  have hvy : (h v : T) = y := congrArg Subtype.val hv
  have hvU (hav : a ≤ ‖(v : T)‖) : Phi (y, 0) ∈ U := by
    rw [← hvy, ← hHval v]
    exact hleftover v v.property hav
  by_cases hva : ‖(v : T)‖ ≤ a
  · let x := split.symm (a⁻¹ • (v : T), (0 : Z))
    have hsplitx : split x = (a⁻¹ • (v : T), (0 : Z)) := split.apply_symm_apply _
    have hscale : a • (split x).1 = (v : T) := by
      rw [hsplitx, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    have hxp : x ∈ p.source := by
      apply (hsource x).mpr
      rw [hscale, mem_ball_zero_iff]
      exact hva.trans_lt hab.2
    have hc0 : c (0 : Z) = 0 := hcfix 0 (by simp)
    have hpx : p x = Phi (y, 0) := by
      rw [hpFormula, hscale, hsplitx, hc0, smul_zero, hHval v, hvy]
    apply Or.inr
    refine ⟨x, ?_, hpx⟩
    rcases lt_or_eq_of_le hva with hlt | heq
    · apply Or.inl
      rw [mem_ball_zero_iff, ← norm_handleCoordinateSplit J x]
      change ‖split x‖ < 1
      rw [hsplitx, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _),
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
      exact (inv_mul_lt_iff₀ ha).mpr (by simpa using hlt)
    · apply Or.inr
      refine ⟨⟨hxp, ?_⟩, ?_⟩
      · change p x ∈ U
        rw [hpx]
        exact hvU heq.ge
      · intro i hi
        have hv0 := congrFun (congrArg Prod.snd hsplitx) ⟨i, hi⟩
        change |x i| < 1
        change x i = 0 at hv0
        rw [hv0, abs_zero]
        exact zero_lt_one
  · have hav : a < ‖(v : T)‖ := lt_of_not_ge hva
    apply Or.inl
    refine ⟨hvU hav.le, ?_⟩
    rintro ⟨x, hx, hxy⟩
    rw [hpFormula] at hxy
    have hfirst := congrArg Prod.fst (Phi.injective hxy)
    have hunit : a • (split x).1 ∈ closedBall (0 : T) 1 :=
      mem_closedBall_zero_iff.mpr ((hscaled x hx.1).trans ha1.le)
    have hhEq : h ⟨a • (split x).1, hunit⟩ = h v := by
      apply Subtype.ext
      rw [← hHval ⟨_, hunit⟩, hvy]
      exact hfirst
    have hcoord : a • (split x).1 = (v : T) := congrArg Subtype.val (h.injective hhEq)
    exact (not_lt_of_ge (hcoord ▸ hscaled x hx.1)) hav

end PoincareConjecture.M76
