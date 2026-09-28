import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMeridianBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "Q" => sphere (0 : V2) 1
local notation "C14" => AddCircle (4 * (7 / 2 : ℝ))

private theorem square_boundary_coordinates (x : V2) :
    x ∈ Q ↔ (x 0 ∈ Icc (-1 : ℝ) 1 ∧ x 1 ∈ Icc (-1 : ℝ) 1) ∧
      ¬(x 0 ∈ Ioo (-1 : ℝ) 1 ∧ x 1 ∈ Ioo (-1 : ℝ) 1) := by
  have hle : ‖x‖ ≤ 1 ↔ x 0 ∈ Icc (-1 : ℝ) 1 ∧ x 1 ∈ Icc (-1 : ℝ) 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Fin.forall_fin_two, Real.norm_eq_abs, abs_le, mem_Icc]
  have hlt : ‖x‖ < 1 ↔ x 0 ∈ Ioo (-1 : ℝ) 1 ∧ x 1 ∈ Ioo (-1 : ℝ) 1 := by
    rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    simp only [Fin.forall_fin_two, Real.norm_eq_abs, abs_lt, mem_Ioo]
  rw [mem_sphere_zero_iff_norm, ← hle, ← hlt]
  exact ⟨fun h => ⟨h.le, not_lt_of_ge h.ge⟩,
    fun h => le_antisymm h.1 (le_of_not_gt h.2)⟩

private theorem shell_frontier_coordinates (y : W) :
    y ∈ frontier squareShell ↔
      (y.1 ∈ Icc (-1 : ℝ) 1 ∧ ‖y.2‖ ∈ Icc (3 / 2 : ℝ) 2) ∧
      ¬(y.1 ∈ Ioo (-1 : ℝ) 1 ∧ ‖y.2‖ ∈ Ioo (3 / 2 : ℝ) 2) := by
  have hrep : ((norm : (ℝ × ℝ) → ℝ) ⁻¹' Icc (3 / 2) 2) =
      closedBall 0 2 ∩ (ball 0 (3 / 2))ᶜ := by
    ext v
    simp only [mem_preimage, mem_Icc, mem_inter_iff, mem_compl_iff,
      mem_closedBall_zero_iff, mem_ball_zero_iff, not_lt]
    exact and_comm
  have hi : interior squareShell =
      Ioo (-1) 1 ×ˢ ((norm : (ℝ × ℝ) → ℝ) ⁻¹' Ioo (3 / 2) 2) := by
    rw [squareShell, interior_prod_eq, interior_Icc, hrep, interior_inter,
      interior_closedBall _ (by norm_num), interior_compl,
      closure_ball _ (by norm_num)]
    congr 1
    ext v
    simp only [mem_inter_iff, mem_compl_iff, mem_ball_zero_iff,
      mem_closedBall_zero_iff, not_le, mem_preimage, mem_Ioo]
    exact and_comm
  have hc : IsClosed squareShell :=
    isClosed_Icc.prod (isClosed_Icc.preimage continuous_norm)
  rw [frontier, hc.closure_eq, hi]
  rfl

private theorem band_norm {x : V2} (hx : x 1 ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    ‖(standardMeridianBandMap (x, t)).2‖ = 7 / 4 + x 1 / 4 := by
  have hw : 4 * |-(x 1) / 4| < (7 / 2 : ℝ) := by
    have h : |-(x 1) / 4| ≤ (1 / 4 : ℝ) :=
      abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
    linarith
  have hd := PLAnnularStrip.depth_annulusMap
    (by norm_num : (0 : ℝ) < 7 / 2) hw (t : C14)
  have he : (standardMeridianBandMap (x, t)).2 + ((7 / 4 : ℝ), (7 / 4 : ℝ)) =
      PLAnnularStrip.annulusMap (7 / 2) (by norm_num) ((t : C14), -x 1 / 4) := by
    change -((7 / 4 : ℝ), (7 / 4 : ℝ)) + _ + _ = _
    abel
  have h := depth_centered (standardMeridianBandMap (x, t)).2
  rw [he, hd] at h
  linarith

private theorem band_mem_frontier_iff {x : V2}
    (hx : x 1 ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    standardMeridianBandMap (x, t) ∈ frontier squareShell ↔ x ∈ Q := by
  rw [shell_frontier_coordinates, band_norm hx, square_boundary_coordinates]
  change ((x 0 ∈ Icc (-1 : ℝ) 1 ∧
      7 / 4 + x 1 / 4 ∈ Icc (3 / 2 : ℝ) 2) ∧
      ¬(x 0 ∈ Ioo (-1 : ℝ) 1 ∧ 7 / 4 + x 1 / 4 ∈ Ioo (3 / 2 : ℝ) 2)) ↔ _
  have hr : 7 / 4 + x 1 / 4 ∈ Icc (3 / 2 : ℝ) 2 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hri : 7 / 4 + x 1 / 4 ∈ Ioo (3 / 2 : ℝ) 2 ↔
      x 1 ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hri]
  exact ⟨fun h => ⟨⟨h.1.1, hx⟩, h.2⟩, fun h => ⟨⟨h.1.1, hr⟩, h.2⟩⟩

private theorem band_eq_iff {x y : V2 × ℝ} (hx : x.1 ∈ Q) (hy : y.1 ∈ Q) :
    standardMeridianBandMap x = standardMeridianBandMap y ↔
      x.1 = y.1 ∧ (x.2 : C14) = (y.2 : C14) := by
  constructor
  · intro h
    have hx1 := ((square_boundary_coordinates x.1).mp hx).1.2
    have hy1 := ((square_boundary_coordinates y.1).mp hy).1.2
    have hxd : -x.1 1 / 4 ∈ Icc (-(1 / 4 : ℝ)) (1 / 4) :=
      ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
    have hyd : -y.1 1 / 4 ∈ Icc (-(1 / 4 : ℝ)) (1 / 4) :=
      ⟨by linarith [hy1.2], by linarith [hy1.1]⟩
    have h0 : x.1 0 = y.1 0 := congrArg Prod.fst h
    have hf := congrArg Prod.snd h
    change -((7 / 4 : ℝ), (7 / 4 : ℝ)) + _ =
      -((7 / 4 : ℝ), (7 / 4 : ℝ)) + _ at hf
    have hh : ((x.2 : C14), (⟨-x.1 1 / 4, hxd⟩ : Icc (-(1 / 4 : ℝ)) (1 / 4))) =
        ((y.2 : C14), (⟨-y.1 1 / 4, hyd⟩ : Icc (-(1 / 4 : ℝ)) (1 / 4))) :=
      PLAnnularStrip.injective_annulusMap (by norm_num : (0 : ℝ) < 7 / 2)
        (by norm_num : 4 * (1 / 4 : ℝ) < 7 / 2) (add_left_cancel hf)
    have h1 := congrArg (fun p : C14 × Icc (-(1 / 4 : ℝ)) (1 / 4) => (p.2 : ℝ)) hh
    refine ⟨?_, congrArg Prod.fst hh⟩
    ext i
    fin_cases i
    · exact h0
    · change x.1 1 = y.1 1
      change -x.1 1 / 4 = -y.1 1 / 4 at h1
      linarith
  · rintro ⟨hxy, ht⟩
    simp only [standardMeridianBandMap, hxy, ht]

private theorem exists_band_representative {y : W} (hy : y ∈ frontier squareShell) :
    ∃ x ∈ Q, ∃ t ∈ Ico (0 : ℝ) 14, standardMeridianBandMap (x, t) = y := by
  let : Fact (0 < 4 * (7 / 2 : ℝ)) := ⟨by norm_num⟩
  have hyr := ((shell_frontier_coordinates y).mp hy).1.2
  have hrange : y.2 + ((7 / 4 : ℝ), (7 / 4 : ℝ)) ∈
      PLAnnularStrip.squareAnnulus (7 / 2) (1 / 4) := by
    rw [PLAnnularStrip.mem_squareAnnulus_iff_depth, depth_centered]
    constructor <;> linarith [hyr.1, hyr.2]
  rw [← PLAnnularStrip.range_annulusMap
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : 4 * (1 / 4 : ℝ) < 7 / 2)] at hrange
  obtain ⟨⟨z, d⟩, hzd⟩ := hrange
  change PLAnnularStrip.annulusMap (7 / 2) (by norm_num) (z, (d : ℝ)) =
    y.2 + ((7 / 4 : ℝ), (7 / 4 : ℝ)) at hzd
  let t : ℝ := AddCircle.equivIco (4 * (7 / 2 : ℝ)) 0 z
  have ht : t ∈ Ico (0 : ℝ) 14 := by
    simpa only [zero_add, show 4 * (7 / 2 : ℝ) = 14 by norm_num] using
      (AddCircle.equivIco (4 * (7 / 2 : ℝ)) 0 z).property
  have htval : (t : C14) = z := AddCircle.coe_equivIco
  let x : V2 := ![y.1, -4 * (d : ℝ)]
  have hx1 : x 1 ∈ Icc (-1 : ℝ) 1 := by
    change -4 * (d : ℝ) ∈ Icc (-1 : ℝ) 1
    constructor <;> linarith [d.property.1, d.property.2]
  have hxy : standardMeridianBandMap (x, t) = y := by
    change (y.1, -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
      PLAnnularStrip.annulusMap (7 / 2) (by norm_num)
        ((t : C14), -(-4 * (d : ℝ)) / 4)) = y
    rw [htval, show -(-4 * (d : ℝ)) / 4 = d by ring, hzd]
    apply Prod.ext
    · rfl
    · change -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
        (y.2 + ((7 / 4 : ℝ), (7 / 4 : ℝ))) = y.2
      abel
  exact ⟨x, (band_mem_frontier_iff hx1 t).mp (by rwa [hxy]), t, ht, hxy⟩

private theorem band_finitePL_interval {a b : ℝ} (hab : a < b) :
    FinitePiecewiseAffineOn standardMeridianBandMap (Q ×ˢ Icc a b) := by
  have hq : FinitePiecewiseAffineOn (id : V2 → V2) Q := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 2)
    let J := K.frontierSubcomplex (closedBall (0 : V2) 1)
    have hJ := K.frontierSubcomplex_finite (closedBall (0 : V2) 1) hK
    have hJs := K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs
    rw [frontier_closedBall _ one_ne_zero] at hJs
    exact ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩
  have hi : FinitePiecewiseAffineOn (id : ℝ → ℝ) (Icc a b) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc hab
    exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  obtain ⟨K, hK, hKs, _⟩ := hq.prodMap hi
  let s (i : Fin 2) : (V2 × ℝ) →ᴬ[ℝ] ℝ :=
    ((ContinuousLinearMap.proj i : V2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ V2 ℝ)).toContinuousAffineMap
  let t : (V2 × ℝ) →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap
  let g := t.prod ((-(1 / 4 : ℝ)) • s 1)
  have hg : FinitePiecewiseAffineOn g (Q ×ˢ Icc a b) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine g⟩
  have hs : FinitePiecewiseAffineOn (s 0) (Q ×ˢ Icc a b) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (s 0)⟩
  have hlocal := PLAnnularStrip.locallyPiecewiseAffineOn_annulusMap_lift
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : 4 * (1 / 2 : ℝ) < 7 / 2)
  have hcomp := hlocal.comp_finitePiecewiseAffineOn hg (by
    intro p hp
    have hx := ((square_boundary_coordinates p.1).mp hp.1).1.2
    refine ⟨mem_univ _, ?_⟩
    change -(1 / 4 : ℝ) * p.1 1 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)
    constructor <;> linarith [hx.1, hx.2])
  let shift := (ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ)
    (-((7 / 4 : ℝ), (7 / 4 : ℝ)))).toContinuousAffineMap
  apply (hs.prod_mk (hcomp.postcomp shift)).congr
  intro p _
  change (p.1 0, -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
    PLAnnularStrip.annulusMap (7 / 2) (by norm_num)
      ((p.2 : C14), -(1 / 4 : ℝ) * p.1 1)) = _
  rw [show -(1 / 4 : ℝ) * p.1 1 = -p.1 1 / 4 by ring]
  rfl



theorem standardMeridianBandMap_period_endpoint (x : V2) (delta : ℝ) :
    standardMeridianBandMap (x, 14 - delta) =
      standardMeridianBandMap (x, -delta) := by
  have h : ((14 - delta : ℝ) : C14) = ((-delta : ℝ) : C14) := by
    rw [show (14 - delta : ℝ) = -delta + 4 * (7 / 2 : ℝ) by ring]
    exact AddCircle.coe_add_period _ _
  simp only [standardMeridianBandMap, h]




theorem exists_standard_cut_annulus {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ≤ (1 / 4 : ℝ)) :
    ∃ a : (Q ×ˢ Icc delta (14 - delta)) ≃ₜ
        (frontier squareShell \
          (standardMeridianBandMap '' (Q ×ˢ Ioo (-delta) delta)) : Set W),
      a.IsFinitePL ∧
      (∀ p : (Q ×ˢ Icc delta (14 - delta) : Set (V2 × ℝ)),
        (a p : W) = standardMeridianBandMap p) ∧
      (∀ x : Q, ∀ hx : ((x : V2), delta) ∈ Q ×ˢ Icc delta (14 - delta),
        (a ⟨((x : V2), delta), hx⟩ : W) = standardMeridianBandMap (x, delta)) ∧
      ∀ x : Q, ∀ hx : ((x : V2), 14 - delta) ∈ Q ×ˢ Icc delta (14 - delta),
        (a ⟨((x : V2), 14 - delta), hx⟩ : W) = standardMeridianBandMap (x, -delta) := by
  let : Fact (0 < 4 * (7 / 2 : ℝ)) := ⟨by norm_num⟩
  have hwidth : delta < 14 - delta := by linarith
  let R := Q ×ˢ Icc delta (14 - delta)
  let U := standardMeridianBandMap '' (Q ×ˢ Ioo (-delta) delta)
  have hinj : InjOn standardMeridianBandMap R := by
    intro p hp q hq he
    obtain ⟨hx, ht⟩ := (band_eq_iff hp.1 hq.1).mp he
    have hpI : p.2 ∈ Ico delta (delta + 4 * (7 / 2 : ℝ)) :=
      ⟨hp.2.1, by linarith [hp.2.2]⟩
    have hqI : q.2 ∈ Ico delta (delta + 4 * (7 / 2 : ℝ)) :=
      ⟨hq.2.1, by linarith [hq.2.2]⟩
    exact Prod.ext hx ((AddCircle.coe_eq_coe_iff_of_mem_Ico hpI hqI).mp ht)
  have himage : standardMeridianBandMap '' R = frontier squareShell \ U := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hxp := ((square_boundary_coordinates p.1).mp hp.1).1.2
      refine ⟨(band_mem_frontier_iff hxp p.2).mpr hp.1, ?_⟩
      rintro ⟨q, hq, he⟩
      have ht := ((band_eq_iff hq.1 hp.1).mp he).2
      have hqI : q.2 ∈ Ioc (-delta) (-delta + 4 * (7 / 2 : ℝ)) :=
        ⟨hq.2.1, by linarith [hq.2.2]⟩
      have hpI : p.2 ∈ Ioc (-delta) (-delta + 4 * (7 / 2 : ℝ)) :=
        ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hqI hpI).mp ht
      linarith [hq.2.2, hp.2.1]
    · rintro ⟨hy, hnot⟩
      obtain ⟨x, hx, t, ht, hxt⟩ := exists_band_representative hy
      have hlo : delta ≤ t := by
        by_contra h
        exact hnot ⟨(x, t), ⟨hx, by constructor <;> linarith [ht.1]⟩, hxt⟩
      have hhi : t ≤ 14 - delta := by
        by_contra h
        have he : standardMeridianBandMap (x, t - 14) =
            standardMeridianBandMap (x, t) := by
          apply (band_eq_iff hx hx).mpr
          refine ⟨rfl, ?_⟩
          rw [show (t - 14 : ℝ) = t - 4 * (7 / 2 : ℝ) by ring,
            AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
        exact hnot ⟨(x, t - 14), ⟨hx, by constructor <;> linarith [ht.2]⟩,
          he.trans hxt⟩
      exact ⟨(x, t), ⟨hx, hlo, hhi⟩, hxt⟩
  have hPL := band_finitePL_interval hwidth
  obtain ⟨e, _, heval⟩ := hPL.exists_homeomorph_image hinj
  let a := e.trans (Homeomorph.setCongr himage)
  have haval (p : R) : (a p : W) = standardMeridianBandMap p := heval p
  refine ⟨a, ⟨standardMeridianBandMap, hPL, haval⟩, haval, ?_, ?_⟩
  · intro x hx
    exact haval ⟨((x : V2), delta), hx⟩
  · intro x hx
    exact (haval ⟨((x : V2), 14 - delta), hx⟩).trans
      (standardMeridianBandMap_period_endpoint x delta)

end PoincareConjecture.M76.HamiltonIndexOne
