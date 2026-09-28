import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCutSphere
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneDiskProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneStandardCutAnnulus

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

structure HamiltonMarkedCut {B : Set W}
    {e : frontier squareShell ≃ₜ frontier (complementaryRegion B)}
    (P : HamiltonMarkedDiskProduct e) where
  parametrization : frontier (D2 ×ˢ Icc (P.width / 2) (14 - P.width / 2)) ≃ₜ
    frontier P.cutCarrier
  piecewiseAffine : parametrization.IsFinitePL
  side : ∀ x : Q2 ×ˢ Icc (P.width / 2) (14 - P.width / 2),
    ∀ hx : (x : V2 × ℝ) ∈ frontier (D2 ×ˢ Icc (P.width / 2) (14 - P.width / 2)),
    ∀ hs : standardMeridianBandMap x ∈ frontier squareShell,
      (parametrization ⟨x, hx⟩ : W) = e ⟨standardMeridianBandMap x, hs⟩
  lower : ∀ x : D2,
    ∀ hx : ((x : V2), P.width / 2) ∈
      frontier (D2 ×ˢ Icc (P.width / 2) (14 - P.width / 2)),
      (parametrization ⟨((x : V2), P.width / 2), hx⟩ : W) =
        P.map ((x : V2), P.width / 2)
  upper : ∀ x : D2,
    ∀ hx : ((x : V2), 14 - P.width / 2) ∈
      frontier (D2 ×ˢ Icc (P.width / 2) (14 - P.width / 2)),
      (parametrization ⟨((x : V2), 14 - P.width / 2), hx⟩ : W) =
        P.map ((x : V2), -(P.width / 2))
  ball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) P.cutCarrier (frontier P.cutCarrier)

namespace HamiltonMarkedDiskProduct

variable {B : Set W}
  {e : frontier squareShell ≃ₜ frontier (complementaryRegion B)}
  (P : HamiltonMarkedDiskProduct e)

private theorem open_band_iff (x : frontier squareShell) :
    (e x : W) ∈ P.openStrip ↔ (x : W) ∈
      standardMeridianBandMap '' (Q2 ×ˢ Ioo (-(P.width / 2)) (P.width / 2)) := by
  have hhalf : P.width / 2 ≤ P.width := (half_lt_self P.width_pos).le
  have hmap (y : V2 × ℝ) (hy : y ∈ Q2 ×ˢ Ioo (-(P.width / 2)) (P.width / 2)) :
      standardMeridianBandMap y ∈ frontier squareShell := by
    apply standardMeridianBandMap_properties.2.2.1
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2, P.width_le]⟩
  constructor
  · rintro ⟨y, hy, heq⟩
    have hyfull : y ∈ D2 ×ˢ Icc (-P.width) P.width :=
      ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
    have hyQ : y.1 ∈ Q2 := (P.proper y hyfull).mp (heq.symm ▸ (e x).property)
    have hyq : y ∈ Q2 ×ˢ Ioo (-(P.width / 2)) (P.width / 2) := ⟨hyQ, hy.2⟩
    have he := P.lateral ⟨y.1, hyQ⟩ y.2 hyfull.2 (hmap y hyq)
    have hval : (⟨standardMeridianBandMap y, hmap y hyq⟩ : frontier squareShell) = x :=
      e.injective (Subtype.ext (he.symm.trans heq))
    exact ⟨y, hyq, congrArg Subtype.val hval⟩
  · rintro ⟨y, hy, hxy⟩
    have hyfull : y.2 ∈ Icc (-P.width) P.width := by
      constructor <;> linarith [hy.2.1, hy.2.2]
    have hx : (⟨standardMeridianBandMap y, hmap y hy⟩ : frontier squareShell) = x :=
      Subtype.ext hxy
    exact ⟨y, ⟨sphere_subset_closedBall hy.1, hy.2⟩,
      (P.lateral ⟨y.1, hy.1⟩ y.2 hyfull (hmap y hy)).trans (congrArg (fun z => (e z : W)) hx)⟩

private theorem exists_endpoint_disks :
    ∃ caps : (D2 ×ˢ ({P.width / 2, 14 - P.width / 2} : Set ℝ)) ≃ₜ P.endDisks,
      caps.IsFinitePL ∧
      (∀ (x : D2) (hx : ((x : V2), P.width / 2) ∈
          D2 ×ˢ ({P.width / 2, 14 - P.width / 2} : Set ℝ)),
        (caps ⟨((x : V2), P.width / 2), hx⟩ : W) = P.map ((x : V2), P.width / 2)) ∧
      ∀ (x : D2) (hx : ((x : V2), 14 - P.width / 2) ∈
          D2 ×ˢ ({P.width / 2, 14 - P.width / 2} : Set ℝ)),
        (caps ⟨((x : V2), 14 - P.width / 2), hx⟩ : W) =
          P.map ((x : V2), -(P.width / 2)) := by
  let delta := P.width / 2
  let beta := 14 - delta
  have hd : 0 < delta := half_pos P.width_pos
  have hdsmall : delta ≤ (1 / 4 : ℝ) := by dsimp [delta]; linarith [P.width_le]
  have hden : 0 < 7 - delta := by linarith
  have hlt : delta < beta := by dsimp [beta]; linarith
  let R := D2 ×ˢ ({delta, beta} : Set ℝ)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := isFinitePLBallPair_Icc hlt
  let T := J.frontierSubcomplex (Icc delta beta)
  have hT : T.faces.Finite := J.frontierSubcomplex_finite _ hJ
  have hTs : T.space = ({delta, beta} : Set ℝ) := by
    rw [J.frontierSubcomplex_space isClosed_Icc (convex_Icc _ _)
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr hlt) hJs, frontier_Icc hlt.le]
  obtain ⟨L, hL, hLs, _⟩ := K.exists_finite_triangulation_prod T hK hT
  have hLR : L.space = R := by rw [hLs, hKs, hTs]
  let c : V2 × ℝ →ᴬ[ℝ] V2 × ℝ :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((delta / (7 - delta)) • (ContinuousAffineMap.const ℝ (V2 × ℝ) 7 -
        (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap))
  have hc (x : V2 × ℝ) : c x = (x.1, delta / (7 - delta) * (7 - x.2)) := rfl
  have hlo (x : V2) : c (x, delta) = (x, delta) := by
    rw [hc, div_mul_cancel₀ _ hden.ne']
  have hhi (x : V2) : c (x, beta) = (x, -delta) := by
    rw [hc]
    apply Prod.ext
    · rfl
    · dsimp [beta]
      field_simp [hden.ne']
      ring
  have hcimage : c '' R = D2 ×ˢ ({-delta, delta} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have ht : y.2 = delta ∨ y.2 = beta := hy.2
      rcases ht with ht | ht
      · have he : y = (y.1, delta) := Prod.ext rfl ht
        rw [he, hlo]
        exact ⟨hy.1, Or.inr rfl⟩
      · have he : y = (y.1, beta) := Prod.ext rfl ht
        rw [he, hhi]
        exact ⟨hy.1, Or.inl rfl⟩
    · rintro ⟨hx, ht⟩
      rcases ht with ht | ht
      · refine ⟨(x.1, beta), ⟨hx, Or.inr rfl⟩, ?_⟩
        rw [hhi]
        exact Prod.ext rfl ht.symm
      · refine ⟨(x.1, delta), ⟨hx, Or.inl rfl⟩, ?_⟩
        rw [hlo]
        exact Prod.ext rfl ht.symm
  have hcfull : MapsTo c R (D2 ×ˢ Icc (-P.width) P.width) := by
    intro x hx
    have h := hcimage.subset (mem_image_of_mem c hx)
    refine ⟨h.1, ?_⟩
    rcases h.2 with ht | ht <;> rw [ht] <;>
      constructor <;> dsimp [delta] <;> linarith [P.width_pos]
  have hcinj : Function.Injective c := by
    intro x y hxy
    have hx := congrArg Prod.fst hxy
    have ht := congrArg Prod.snd hxy
    change delta / (7 - delta) * (7 - x.2) = delta / (7 - delta) * (7 - y.2) at ht
    have hxy' := mul_left_cancel₀ (div_pos hd hden).ne' ht
    exact Prod.ext hx (by linarith)
  have hcPL : FinitePiecewiseAffineOn c R :=
    ⟨L, hL, hLR, L.affineOnFaces_affine c⟩
  have hf := P.piecewiseAffine.comp hcPL hcfull
  have hfinj : InjOn (P.map ∘ c) R := fun x hx y hy hxy =>
    hcinj (P.injective (hcfull hx) (hcfull hy) hxy)
  have himage : (P.map ∘ c) '' R = P.endDisks := by
    rw [image_comp, hcimage]
    rfl
  obtain ⟨q, hq, hqval⟩ := hf.exists_homeomorph_image hfinj
  let caps := q.trans (Homeomorph.setCongr himage)
  refine ⟨caps, hq.setCongr rfl himage, ?_, ?_⟩
  · intro x hx
    change (q ⟨((x : V2), delta), hx⟩ : W) = _
    rw [hqval]
    change P.map (c ((x : V2), delta)) = _
    rw [hlo]
  · intro x hx
    change (q ⟨((x : V2), beta), hx⟩ : W) = _
    rw [hqval]
    change P.map (c ((x : V2), beta)) = _
    rw [hhi]

theorem exists_marked_cut_frontier (he : e.IsFinitePL)
    (hR : IsCompact (complementaryRegion B)) : Nonempty (HamiltonMarkedCut P) := by
  let delta := P.width / 2
  let beta := 14 - delta
  have hd : 0 < delta := half_pos P.width_pos
  have hsmall : delta ≤ (1 / 4 : ℝ) := by dsimp [delta]; linarith [P.width_le]
  have hdeltaP : delta ≤ P.width := (half_lt_self P.width_pos).le
  have hlt : delta < beta := by dsimp [beta]; linarith
  let R0 := frontier squareShell \
    (standardMeridianBandMap '' (Q2 ×ˢ Ioo (-delta) delta))
  let R1 := frontier (complementaryRegion B) \ P.openStrip
  obtain ⟨a, ha, haval, _, _⟩ := exists_standard_cut_annulus hd hsmall
  have hmembership (x : frontier squareShell) :
      (x : W) ∈ R0 ↔ (e x : W) ∈ R1 := by
    change ((x : W) ∈ frontier squareShell ∧ (x : W) ∉
        standardMeridianBandMap '' (Q2 ×ˢ Ioo (-delta) delta)) ↔
      ((e x : W) ∈ frontier (complementaryRegion B) ∧ (e x : W) ∉ P.openStrip)
    exact ⟨fun hx => ⟨(e x).property, fun h => hx.2 ((P.open_band_iff x).mp h)⟩,
      fun hx => ⟨x.property, fun h => hx.2 ((P.open_band_iff x).mpr h)⟩⟩
  let r : R0 ≃ₜ R1 := e.restrictSubsets sdiff_subset sdiff_subset hmembership
  have hr : r.IsFinitePL := by
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := ha.symm
    exact he.restrictSubsets sdiff_subset sdiff_subset hmembership K hK hKs
  let side : (Q2 ×ˢ Icc delta beta) ≃ₜ R1 := a.trans r
  have hside : side.IsFinitePL := ha.trans hr
  have hstd (x : Q2 ×ˢ Icc delta beta) : standardMeridianBandMap x ∈ frontier squareShell := by
    rw [← haval x]
    exact (a x).property.1
  have hsideval (x : Q2 ×ˢ Icc delta beta)
      (hx : standardMeridianBandMap x ∈ frontier squareShell) :
      (side x : W) = e ⟨standardMeridianBandMap x, hx⟩ := by
    change (e ⟨(a x : W), (a x).property.1⟩ : W) = _
    exact congrArg (fun y : frontier squareShell => (e y : W)) (Subtype.ext (haval x))
  have hsmallFull (t : ℝ) (ht : t ∈ Icc (-delta) delta) :
      t ∈ Icc (-P.width) P.width :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hband (x : Q2) (t : ℝ) (ht : t ∈ Icc (-delta) delta) :
      standardMeridianBandMap ((x : V2), t) ∈ frontier squareShell := by
    apply standardMeridianBandMap_properties.2.2.1
    exact ⟨x.property, by constructor <;> linarith [ht.1, ht.2]⟩
  have hloTime : delta ∈ Icc (-delta) delta := ⟨by linarith, le_rfl⟩
  have hhiTime : -delta ∈ Icc (-delta) delta := ⟨le_rfl, by linarith⟩
  have hsideLower (x : Q2) (hx : ((x : V2), delta) ∈ Q2 ×ˢ Icc delta beta) :
      (side ⟨((x : V2), delta), hx⟩ : W) = P.map ((x : V2), delta) := by
    rw [hsideval _ (hband x delta hloTime)]
    exact (P.lateral x delta (hsmallFull delta hloTime) (hband x delta hloTime)).symm
  have hsideUpper (x : Q2) (hx : ((x : V2), beta) ∈ Q2 ×ˢ Icc delta beta) :
      (side ⟨((x : V2), beta), hx⟩ : W) = P.map ((x : V2), -delta) := by
    rw [hsideval _ (hstd ⟨((x : V2), beta), hx⟩)]
    have hperiod : standardMeridianBandMap ((x : V2), beta) =
        standardMeridianBandMap ((x : V2), -delta) :=
      standardMeridianBandMap_period_endpoint x delta
    have hp := congrArg (fun y : frontier squareShell => (e y : W))
      (show (⟨standardMeridianBandMap ((x : V2), beta), hstd ⟨((x : V2), beta), hx⟩⟩ :
        frontier squareShell) = ⟨standardMeridianBandMap ((x : V2), -delta),
          hband x (-delta) hhiTime⟩ from Subtype.ext hperiod)
    exact hp.trans (P.lateral x (-delta) (hsmallFull (-delta) hhiTime)
      (hband x (-delta) hhiTime)).symm
  obtain ⟨caps, hcaps, hcapsLower, hcapsUpper⟩ := P.exists_endpoint_disks
  have hoverlap (x : Q2 ×ˢ Icc delta beta) :
      (x : V2 × ℝ).2 ∈ ({delta, beta} : Set ℝ) ↔ (side x : W) ∈ P.endDisks := by
    rcases x with ⟨⟨y, t⟩, hy, ht⟩
    constructor
    · intro he
      change t = delta ∨ t = beta at he
      rcases he with he | he
      · subst t
        exact ⟨(y, delta), ⟨sphere_subset_closedBall hy, Or.inr rfl⟩,
          (hsideLower ⟨y, hy⟩ ⟨hy, ht⟩).symm⟩
      · subst t
        exact ⟨(y, -delta), ⟨sphere_subset_closedBall hy, Or.inl rfl⟩,
          (hsideUpper ⟨y, hy⟩ ⟨hy, ht⟩).symm⟩
    · rintro ⟨⟨v, s⟩, hv, hvs⟩
      have hsends : s = -delta ∨ s = delta := hv.2
      have hst : s ∈ Icc (-delta) delta := by
        rcases hsends with hs | hs <;> rw [hs] <;> constructor <;> linarith
      have hvQ : v ∈ Q2 := (P.proper (v, s) ⟨hv.1, hsmallFull s hst⟩).mp
        (hvs.symm ▸ (side ⟨(y, t), hy, ht⟩).property.1)
      rcases hsends with hs | hs
      · subst s
        have hbmem : (v, beta) ∈ Q2 ×ˢ Icc delta beta := ⟨hvQ, hlt.le, le_rfl⟩
        have hh := side.injective (Subtype.ext
          ((hsideUpper ⟨v, hvQ⟩ hbmem).trans hvs))
        have ht' : beta = t := congrArg (fun z : Q2 ×ˢ Icc delta beta => (z : V2 × ℝ).2) hh
        exact Or.inr ht'.symm
      · subst s
        have hamem : (v, delta) ∈ Q2 ×ˢ Icc delta beta := ⟨hvQ, le_rfl, hlt.le⟩
        have hh := side.injective (Subtype.ext
          ((hsideLower ⟨v, hvQ⟩ hamem).trans hvs))
        have ht' : delta = t := congrArg (fun z : Q2 ×ˢ Icc delta beta => (z : V2 × ℝ).2) hh
        exact Or.inl ht'.symm
  have hagree (x : V2 × ℝ) (hs : x ∈ Q2 ×ˢ Icc delta beta)
      (hc : x ∈ D2 ×ˢ ({delta, beta} : Set ℝ)) :
      (side ⟨x, hs⟩ : W) = caps ⟨x, hc⟩ := by
    rcases x with ⟨x, t⟩
    have htends : t = delta ∨ t = beta := hc.2
    rcases htends with ht | ht
    · subst t
      exact (hsideLower ⟨x, hs.1⟩ hs).trans (hcapsLower ⟨x, hc.1⟩ hc).symm
    · subst t
      exact (hsideUpper ⟨x, hs.1⟩ hs).trans (hcapsUpper ⟨x, hc.1⟩ hc).symm
  obtain ⟨hcut, _, hfront, _, _, hne⟩ := P.cut_geometry hR
  obtain ⟨H, hH, hHside, hHcaps⟩ :=
    exists_capped_annulus_frontier_map hlt side caps hside hcaps hoverlap hagree
  let F := H.trans (Homeomorph.setCongr hfront.symm)
  have hF : F.IsFinitePL := hH.setCongr rfl hfront.symm
  have hball := isFinitePLBallPair_of_capped_annulus_frontier
    (by simp [Module.finrank_prod] : Module.finrank ℝ W = 3)
    hcut hne hfront hlt side caps hside hcaps hoverlap hagree
  refine ⟨⟨F, hF, ?_, ?_, ?_, hball⟩⟩
  · intro x hx hs
    exact (hHside x hx).trans (hsideval x hs)
  · intro x hx
    have hp : ((x : V2), delta) ∈ D2 ×ˢ ({delta, beta} : Set ℝ) :=
      ⟨x.property, Or.inl rfl⟩
    exact (hHcaps ⟨((x : V2), delta), hp⟩ hx).trans (hcapsLower x hp)
  · intro x hx
    have hp : ((x : V2), beta) ∈ D2 ×ˢ ({delta, beta} : Set ℝ) :=
      ⟨x.property, Or.inr rfl⟩
    exact (hHcaps ⟨((x : V2), beta), hp⟩ hx).trans (hcapsUpper x hp)

end HamiltonMarkedDiskProduct
end PoincareConjecture.M76.HamiltonIndexOne
