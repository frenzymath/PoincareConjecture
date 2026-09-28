import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProductBandContainment
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardPrism
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)




theorem hamilton_half_boundary_models {w : ℝ} (hw : 0 < w) :
    IsFinitePLBallPair (ℝ × ℝ)
      ((D2 ×ˢ {(0 : ℝ)}) ∪ (Q2 ×ˢ Icc 0 w)) (Q2 ×ˢ {w}) ∧
      FinitePiecewiseAffineOn (id : V2 × ℝ → V2 × ℝ) (Q2 ×ˢ Icc 0 w) ∧
      IsFinitePLBallPair (ℝ × ℝ) (D2 ×ˢ {w}) (Q2 ×ˢ {w}) := by
  let cL := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let c := cL.toContinuousAffineEquiv
  let a := (cL.prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousAffineEquiv
  have hcbase : c '' CoordinateHalfBoxes.base 1 = D2 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      fin_cases i
      · change ‖y.1‖ ≤ 1
        rw [Real.norm_eq_abs]
        exact abs_le.mpr hy.1
      · change ‖y.2‖ ≤ 1
        rw [Real.norm_eq_abs]
        exact abs_le.mpr hy.2
    · intro hx
      refine ⟨c.symm x, ?_, c.apply_symm_apply x⟩
      have hn := (pi_norm_le_iff_of_nonneg zero_le_one).mp
        (mem_closedBall_zero_iff.mp hx)
      change x 0 ∈ Icc (-1 : ℝ) 1 ∧ x 1 ∈ Icc (-1 : ℝ) 1
      exact ⟨abs_le.mp (by simpa only [Real.norm_eq_abs] using hn 0),
        abs_le.mp (by simpa only [Real.norm_eq_abs] using hn 1)⟩
  have hcfront : c '' CoordinateHalfBoxes.baseBoundary 1 = Q2 := by
    rw [← (CoordinateHalfBoxes.base_ballPair zero_lt_one).frontier_eq_of_finrank_eq rfl]
    calc
      c '' frontier (CoordinateHalfBoxes.base 1) =
          frontier (c '' CoordinateHalfBoxes.base 1) := c.toHomeomorph.image_frontier _
      _ = Q2 := by rw [hcbase, frontier_closedBall _ one_ne_zero]
  have haprod (S : Set (ℝ × ℝ)) (T : Set ℝ) : a '' (S ×ˢ T) = (c '' S) ×ˢ T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_image_of_mem c hy.1, hy.2⟩
    · rintro ⟨⟨y, hy, he⟩, ht⟩
      exact ⟨(y, x.2), ⟨hy, ht⟩, Prod.ext he rfl⟩
  have hsource : a '' HamiltonIndexTwoStandard.lowerOuter 0 w =
      (D2 ×ˢ {(0 : ℝ)}) ∪ (Q2 ×ˢ Icc 0 w) := by
    rw [HamiltonIndexTwoStandard.lowerOuter, HamiltonIndexTwoStandard.band,
      HamiltonIndexTwoStandard.endDisk, image_union, haprod, haprod,
      hcfront, hcbase, union_comm]
  have hrim : a '' HamiltonIndexTwoStandard.endRim w = Q2 ×ˢ {w} := by
    rw [HamiltonIndexTwoStandard.endRim, haprod, hcfront]
  have hball := (HamiltonIndexTwoStandard.lowerOuter_ballPair hw).affine_image
    a.toContinuousAffineMap a.injective.injOn
  have hside := (HamiltonIndexTwoStandard.band_identity_finitePL hw).precomp_affineEquiv
    a.symm
  have hside' := hside.postcomp a.toContinuousAffineMap
  have hsideimage : a '' HamiltonIndexTwoStandard.band 0 w = Q2 ×ˢ Icc 0 w := by
    rw [HamiltonIndexTwoStandard.band, haprod, hcfront]
  have hendimage : a '' HamiltonIndexTwoStandard.endDisk w = D2 ×ˢ {w} := by
    rw [HamiltonIndexTwoStandard.endDisk, haprod, hcbase]
  refine ⟨?_, ?_, ?_⟩
  · change IsFinitePLBallPair (ℝ × ℝ) (a '' HamiltonIndexTwoStandard.lowerOuter 0 w)
      (a '' HamiltonIndexTwoStandard.endRim w) at hball
    rwa [hsource, hrim] at hball
  · change FinitePiecewiseAffineOn (fun x => a (a.symm x))
      (a '' HamiltonIndexTwoStandard.band 0 w) at hside'
    rw [hsideimage] at hside'
    exact hside'.congr (fun x _ => a.apply_symm_apply x)
  · have h := (HamiltonIndexTwoStandard.endDisk_ballPair w).affine_image
      a.toContinuousAffineMap a.injective.injOn
    change IsFinitePLBallPair (ℝ × ℝ) (a '' HamiltonIndexTwoStandard.endDisk w)
      (a '' HamiltonIndexTwoStandard.endRim w) at h
    rwa [hendimage, hrim] at h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_marked_half_boundary_parametrization {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b) (hb : b.IsFinitePL)
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    {w : ℝ} (hw : 0 < w) (hwsmall : w ≤ 1 / 4)
    (hband : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))) :
    ∃ H : (((D2 ×ˢ {(0 : ℝ)}) ∪ (Q2 ×ˢ Icc 0 w)) : Set (V2 × ℝ)) ≃ₜ
        (D ∪ F '' (Q2 ×ˢ Icc 0 w) : Set E), H.IsFinitePL ∧
      (∀ (x : D2) (hx : ((x : V2), (0 : ℝ)) ∈
          (D2 ×ˢ {(0 : ℝ)}) ∪ (Q2 ×ˢ Icc 0 w)),
        (H ⟨((x : V2), 0), hx⟩ : E) = b x) ∧
      (∀ (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc 0 w),
        (H ⟨p, Or.inr hp⟩ : E) = F p) ∧
      (∀ x : ((D2 ×ˢ {(0 : ℝ)}) ∪ (Q2 ×ˢ Icc 0 w) : Set (V2 × ℝ)),
        (x : V2 × ℝ) ∈ Q2 ×ˢ {w} ↔ (H x : E) ∈ F '' (Q2 ×ˢ {w})) ∧
      IsFinitePLBallPair (ℝ × ℝ) (D ∪ F '' (Q2 ×ˢ Icc 0 w))
        (F '' (Q2 ×ˢ {w})) := by
  classical
  let base : Set (V2 × ℝ) := D2 ×ˢ {(0 : ℝ)}
  let side : Set (V2 × ℝ) := Q2 ×ˢ Icc 0 w
  let rim : Set (V2 × ℝ) := Q2 ×ˢ {w}
  let G := D ∪ F '' side
  obtain ⟨hsource, hsideid, _⟩ := hamilton_half_boundary_models hw
  obtain ⟨j, _, hjP, _, hcoord, _, _⟩ :=
    exists_prescribed_band_coordinates P F hFinj hFfront hcenter hwsmall hband
  have hsidefull : side ⊆ Q2 ×ˢ I := fun p hp =>
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hsideband : side ⊆ Q2 ×ˢ Icc (-w) w := fun p hp =>
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hbasej (x : D2) : j (b x) = ((x : V2), (0 : ℝ)) := by
    rw [← P.central x]
    exact hjP _ ⟨x.property, by norm_num⟩
  have hcontact (x : D2) : (b x : E) ∈ F '' side ↔ (x : V2) ∈ Q2 := by
    constructor
    · rintro ⟨p, hp, hpv⟩
      have h := (hcoord p (hsideband hp)).1
      rw [hpv, hbasej] at h
      exact h
    · intro hx
      refine ⟨((x : V2), 0), ⟨hx, le_rfl, hw.le⟩, ?_⟩
      exact (hcenter x hx).trans (P.central x)
  obtain ⟨u, hu, huv⟩ := hb
  let f : (V2 × ℝ) → E := fun p => if p.2 = 0 then u p.1 else F p
  have hfbase (p : V2 × ℝ) (hp : p ∈ base) : f p = b ⟨p.1, hp.1⟩ := by
    have ht : p.2 = 0 := hp.2
    rw [show f p = u p.1 by exact if_pos ht]
    exact (huv ⟨p.1, hp.1⟩).symm
  have hfside (p : V2 × ℝ) (hp : p ∈ side) : f p = F p := by
    by_cases ht : p.2 = 0
    · change (if p.2 = 0 then u p.1 else F p) = F p
      rw [if_pos ht]
      have he : p = (p.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [he, hcenter p.1 hp.1, P.central ⟨p.1, sphere_subset_closedBall hp.1⟩]
      exact (huv ⟨p.1, sphere_subset_closedBall hp.1⟩).symm
    · exact if_neg ht
  have hbaseball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod_singleton (0 : ℝ)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKb, _⟩, _⟩, _⟩ := hbaseball
  have hfst : FinitePiecewiseAffineOn (Prod.fst : V2 × ℝ → V2) base :=
    ⟨K, hK, hKb, K.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap⟩
  have hfPLbase : FinitePiecewiseAffineOn f base :=
    (hu.comp hfst (fun _ hp => hp.1)).congr (fun p hp => by
      rw [hfbase p hp]
      exact (huv ⟨p.1, hp.1⟩).symm)
  obtain ⟨J, hJ, hJs, _⟩ := hsideid
  have hfPLside : FinitePiecewiseAffineOn f side := by
    have h := hF.restrict J hJ (hJs.subset.trans hsidefull)
    rw [hJs] at h
    exact h.congr (fun p hp => (hfside p hp).symm)
  have hfPL : FinitePiecewiseAffineOn f (base ∪ side) :=
    finitePiecewiseAffineOn_union hfPLbase hfPLside
  have hcross (p q : V2 × ℝ) (hp : p ∈ base) (hq : q ∈ side)
      (he : f p = f q) : p = q := by
    have hpq : p.1 ∈ Q2 := (hcontact ⟨p.1, hp.1⟩).mp
      ⟨q, hq, (hfside q hq).symm.trans (he.symm.trans (hfbase p hp))⟩
    have hpfull : p ∈ Q2 ×ˢ I := ⟨hpq, by
      have ht : p.2 = 0 := hp.2
      rw [ht]
      norm_num⟩
    have hpside : p ∈ side := ⟨hpq, by
      have ht : p.2 = 0 := hp.2
      rw [ht]
      exact ⟨le_rfl, hw.le⟩⟩
    exact hFinj hpfull (hsidefull hq)
      ((hfside p hpside).symm.trans (he.trans (hfside q hq)))
  have hfi : InjOn f (base ∪ side) := by
    intro p hp q hq he
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · have he' := b.injective (Subtype.ext
        ((hfbase p hp).symm.trans (he.trans (hfbase q hq))))
      exact Prod.ext (congrArg Subtype.val he') (hp.2.trans hq.2.symm)
    · exact hcross p q hp hq he
    · exact (hcross q p hq hp he.symm).symm
    · exact hFinj (hsidefull hp) (hsidefull hq)
        ((hfside p hp).symm.trans (he.trans (hfside q hq)))
  have himage : f '' (base ∪ side) = G := by
    ext y
    constructor
    · rintro ⟨p, hp | hp, rfl⟩
      · rw [hfbase p hp]
        exact Or.inl (b ⟨p.1, hp.1⟩).property
      · exact Or.inr ⟨p, hp, (hfside p hp).symm⟩
    · rintro (hy | ⟨p, hp, rfl⟩)
      · let x := b.symm ⟨y, hy⟩
        have hxbase : ((x : V2), (0 : ℝ)) ∈ base := ⟨x.property, rfl⟩
        refine ⟨((x : V2), 0), Or.inl hxbase, ?_⟩
        rw [hfbase ((x : V2), (0 : ℝ)) hxbase]
        exact congrArg Subtype.val (b.apply_symm_apply ⟨y, hy⟩)
      · exact ⟨p, Or.inr hp, hfside p hp⟩
  have hrimside : rim ⊆ side := fun p hp => ⟨hp.1, by
    have ht : p.2 = w := hp.2
    rw [ht]
    exact ⟨hw.le, le_rfl⟩⟩
  have hrimimage : f '' rim = F '' rim := image_congr (fun p hp => hfside p (hrimside hp))
  obtain ⟨H0, _, hH0v⟩ := hfPL.exists_homeomorph_image hfi
  let H := H0.trans (Homeomorph.setCongr himage)
  have hHv (x : (base ∪ side : Set (V2 × ℝ))) : (H x : E) = f x := hH0v x
  have hH : H.IsFinitePL := ⟨f, hfPL, hHv⟩
  have hrimsource : rim ⊆ base ∪ side := hrimside.trans subset_union_right
  refine ⟨H, hH, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hHv ⟨((x : V2), 0), hx⟩).trans
      (hfbase ((x : V2), (0 : ℝ)) (show ((x : V2), (0 : ℝ)) ∈ base from ⟨x.property, rfl⟩))
  · intro p hp
    exact (hHv ⟨p, Or.inr hp⟩).trans (hfside p hp)
  · intro x
    rw [hHv, ← hrimimage]
    constructor
    · exact mem_image_of_mem f
    · rintro ⟨y, hy, hyx⟩
      exact hfi (hrimsource hy) x.property hyx ▸ hy
  · have h := hsource.image hfPL hfi
    rwa [himage, hrimimage] at h

end PoincareConjecture.M76.HamiltonIndexOne
