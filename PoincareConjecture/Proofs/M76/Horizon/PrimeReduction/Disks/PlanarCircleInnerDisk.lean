import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisMonodromy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.EndpointLoopPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PlanarPLDiskUniqueness
import PoincareConjecture.Proofs.M76.Mathlib.DisjointPolygonNesting
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
open Dehn
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => (P2 × ℝ)



theorem exists_inner_disk_of_planar_circle_strip
    {n : ℕ} (P : Polygon P2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) {D : Set P2}
    (hD : IsFinitePLBallPair P2 D (P.boundary ℝ))
    {β : ℝ} (hβ : 0 < β) (f : P2 → P2)
    (hf : FinitePiecewiseAffineOn f (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      f x = f y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β)))
    (haxis : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      f x ∈ P.boundary ℝ ↔ x.1 = 0) :
    ∃ positive : Bool,
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 β,
        f (if positive then c else -c, t) ∈ D \ P.boundary ℝ) ∧
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 β,
        f (if positive then -c else c, t) ∉ D) ∧
      ∃ (m : ℕ) (Q : Polygon P2 (m + 3)),
        Function.Injective Q ∧ Q.HasSimplicialEdges ∧
        Q.boundary ℝ = (fun t => f (if positive then 1 / 2 else -1 / 2, t)) '' Icc 0 β ∧
        IsFinitePLBallPair P2 (closure Q.inside) (Q.boundary ℝ) ∧
        closure Q.inside ⊆ D \ P.boundary ℝ := by
  classical
  have hinj : InjOn f (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 β) := by
    intro x hx y hy heq
    have hx' : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β :=
      ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1.le, hx.2.2.le⟩
    have hy' : y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β :=
      ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2.1.le, hy.2.2.le⟩
    obtain ⟨hxy, ht | ht | ht⟩ := (hfib x hx' y hy').mp heq
    · exact Prod.ext hxy ht
    · exact (hx.2.1.ne' ht.1).elim
    · exact (hy.2.1.ne' ht.1).elim
  obtain hlabels := P.transverse_strip_side_labels hP hPi (by norm_num : (0 : ℝ) < 1)
    hβ hf hinj haxis
  have hside : ∃ positive : Bool,
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 β,
        f (if positive then c else -c, t) ∈ P.inside) ∧
      ∀ c ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 β,
        f (if positive then -c else c, t) ∈ P.outside := by
    rcases hlabels with ⟨hi, ho⟩ | ⟨hi, ho⟩
    · refine ⟨true, fun c hc t ht => hi ⟨(c, t), ⟨hc, ht⟩, rfl⟩, ?_⟩
      intro c hc t ht
      exact ho ⟨(-c, t), ⟨⟨by linarith [hc.2], by linarith [hc.1]⟩, ht⟩, rfl⟩
    · refine ⟨false, ?_, fun c hc t ht => ho ⟨(c, t), ⟨hc, ht⟩, rfl⟩⟩
      intro c hc t ht
      exact hi ⟨(-c, t), ⟨⟨by linarith [hc.2], by linarith [hc.1]⟩, ht⟩, rfl⟩
  obtain ⟨positive, hin, hout⟩ := hside
  have hDeq : D = closure P.inside := hD.eq_closure_polygon_inside P hP hPi
  have hinside : P.inside ⊆ D \ P.boundary ℝ := by
    intro x hx
    exact ⟨hDeq.symm ▸ subset_closure hx, hx.1⟩
  have houtside : P.outside ⊆ Dᶜ := by
    intro x hx hxD
    have hxcl := hDeq.subset hxD
    rw [closure_eq_self_union_frontier, P.frontier_inside hP hPi] at hxcl
    rcases hxcl with hi | hb
    · exact disjoint_left.mp P.disjoint_inside_outside hi hx
    · exact hx.1 hb
  let c : ℝ := if positive then 1 / 2 else -1 / 2
  have hc : c ∈ Icc (-1 : ℝ) 1 := by cases positive <;> norm_num [c]
  let line : ℝ →ᴬ[ℝ] P2 := (ContinuousAffineMap.const ℝ ℝ c).prod
    (β • ContinuousAffineMap.id ℝ ℝ)
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : β * t ∈ Icc 0 β :=
    ⟨mul_nonneg hβ.le ht.1, by nlinarith [ht.2]⟩
  have hlineMap : MapsTo line (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) :=
    fun t ht => ⟨hc, htime t ht⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hline : FinitePiecewiseAffineOn line (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine line⟩
  have hloopPL : FinitePiecewiseAffineOn (f ∘ line) (Icc (0 : ℝ) 1) := hf.comp hline hlineMap
  have hloopfib : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      (f ∘ line) x = (f ∘ line) y ↔
        x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
    intro x hx y hy
    rw [Function.comp_apply, Function.comp_apply, hfib _ (hlineMap hx) _ (hlineMap hy)]
    change c = c ∧ (β * x = β * y ∨ (β * x = 0 ∧ β * y = β) ∨
      (β * y = 0 ∧ β * x = β)) ↔ _
    have heq (x y : ℝ) : β * x = β * y ↔ x = y := mul_right_inj' hβ.ne'
    have hz (x : ℝ) : β * x = 0 ↔ x = 0 := by simpa only [mul_zero] using heq x 0
    have ho (x : ℝ) : β * x = β ↔ x = 1 := by simpa only [mul_one] using heq x 1
    rw [heq, hz, ho, hz, ho]
    tauto
  obtain ⟨m, Q, hQi, hQ, hQb⟩ := exists_polygon_of_endpoint_loop hloopPL hloopfib
  have hloopImage : (f ∘ line) '' Icc (0 : ℝ) 1 =
      (fun t => f (c, t)) '' Icc 0 β := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨β * t, htime t ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t / β, ⟨div_nonneg ht.1 hβ.le, (div_le_one hβ).mpr ht.2⟩, ?_⟩
      change f (c, β * (t / β)) = f (c, t)
      rw [mul_div_cancel₀ _ hβ.ne']
  have hQinside : Q.boundary ℝ ⊆ P.inside := by
    rw [hQb, hloopImage]
    rintro _ ⟨t, ht, rfl⟩
    simpa only [c, neg_div] using hin (1 / 2) (by norm_num) t ht
  exact ⟨positive, fun c hc t ht => hinside (hin c hc t ht),
    fun c hc t ht => houtside (hout c hc t ht), m, Q, hQi, hQ,
    hQb.trans hloopImage, Q.isFinitePLBallPair_closed_inside hQ hQi,
    (P.closure_inside_subset_inside_of_boundary_subset_inside Q hP hPi hQ hQi hQinside).trans hinside⟩





theorem exists_inner_disk_of_identity_circle_tube
    {n : ℕ} (L : Polygon V3 (n + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) {D T : Set V3}
    (hD : IsFinitePLBallPair P2 D (L.boundary ℝ)) (hDT : D ⊆ T)
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F) (hFR : EqOn (F ∘ R) id T)
    {β : ℝ} (hβ : 0 < β) (sigma : C3 → V3)
    (hSigma : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc 0 β))
    (htriangle : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ T ↔ x.1 ∈ signedTubeSheet 0)
    (haxis : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ L.boundary ℝ ↔ x.1 = (0, 0))
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x = sigma y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β))) :
    ∃ positive : Bool,
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 β,
        sigma ((0, if positive then c else -c), t) ∈ D \ L.boundary ℝ) ∧
      (∀ c ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc 0 β,
        sigma ((0, if positive then -c else c), t) ∉ D) ∧
      ∃ (m : ℕ) (P : Polygon V3 (m + 3)) (inner : Set V3),
        Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ =
          (fun t => sigma ((0, if positive then 1 / 2 else -1 / 2), t)) '' Icc 0 β ∧
        IsFinitePLBallPair P2 inner (P.boundary ℝ) ∧
        inner ⊆ D \ L.boundary ℝ := by
  classical
  have hRi : InjOn R T := by
    intro x hx y hy heq
    exact (hFR hx).symm.trans ((congrArg F heq).trans (hFR hy))
  have hLT : L.boundary ℝ ⊆ T := hD.1.trans hDT
  let P := L.affineImage R.toAffineMap
  have hPb : P.boundary ℝ = R '' L.boundary ℝ := L.affineImage_boundary R.toAffineMap
  obtain ⟨hPi, hP, hFPr⟩ := L.affineImage_of_leftInvOn hL hLi R.toAffineMap
    F.toAffineMap (hFR.mono hLT)
  have hDp : IsFinitePLBallPair P2 (R '' D) (P.boundary ℝ) := by
    rw [hPb]
    exact hD.affine_image R (hRi.mono hDT)
  let f : P2 → P2 := R ∘ sigma ∘ signedSheetStripMap 0
  have hstrip (x : P2) (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) :
      sigma (signedSheetStripMap 0 x) ∈ T :=
    (htriangle _ (signedSheetStripMap_mem 0 hx)).mpr (signedSheetStripMap_sheet 0 hx)
  have hf : FinitePiecewiseAffineOn f (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) :=
    (hSigma.comp (signedSheetStripMap_finitePL hβ 0)
      (fun _ hx => signedSheetStripMap_mem 0 hx)).postcomp R
  have hstripfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      f x = f y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β)) := by
    intro x hx y hy
    have heq : f x = f y ↔ sigma (signedSheetStripMap 0 x) = sigma (signedSheetStripMap 0 y) :=
      ⟨fun h => hRi (hstrip x hx) (hstrip y hy) h, fun h => congrArg R h⟩
    rw [heq, hfib _ (signedSheetStripMap_mem 0 hx) _ (signedSheetStripMap_mem 0 hy)]
    simp only [signedSheetStripMap_apply, ↓reduceIte, Prod.mk.injEq, true_and]
  have hstripAxis : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      f x ∈ P.boundary ℝ ↔ x.1 = 0 := by
    intro x hx
    have hmem : f x ∈ P.boundary ℝ ↔ sigma (signedSheetStripMap 0 x) ∈ L.boundary ℝ := by
      rw [hPb]
      constructor
      · rintro ⟨y, hy, heq⟩
        exact hRi (hLT hy) (hstrip x hx) heq ▸ hy
      · exact fun h => mem_image_of_mem R h
    rw [hmem, haxis _ (signedSheetStripMap_mem 0 hx)]
    simp only [signedSheetStripMap_apply, ↓reduceIte, Prod.mk.injEq, true_and]
  obtain ⟨positive, hin, hout, m, Q, hQi, hQ, hQb, hQdisk, hQinside⟩ :=
    exists_inner_disk_of_planar_circle_strip P hP hPi hDp hβ f hf hstripfib hstripAxis
  have hFmem (x : P2) (hx : x ∈ (R '' D) \ P.boundary ℝ) : F x ∈ D \ L.boundary ℝ := by
    obtain ⟨y, hy, hyx⟩ := hx.1
    have hFx : F x = y := (congrArg F hyx.symm).trans (hFR (hDT hy))
    refine ⟨hFx.symm ▸ hy, ?_⟩
    intro hLx
    have hR : R (F x) = x := hRF x
    exact hx.2 (hPb.symm.subset ⟨F x, hLx, hR⟩)
  have hval (c t : ℝ) (hc : c ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc 0 β) :
      F (f (c, t)) = sigma ((0, c), t) := by
    exact hFR (hstrip (c, t) ⟨hc, ht⟩)
  have hsigned (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) 1) (b : Bool) :
      (if b then c else -c) ∈ Icc (-1 : ℝ) 1 := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals constructor <;> linarith [hc.1, hc.2]
  let Q' := Q.affineImage F.toAffineMap
  let inner := F '' closure Q.inside
  have hQ'b : Q'.boundary ℝ = F '' Q.boundary ℝ := Q.affineImage_boundary F.toAffineMap
  refine ⟨positive, ?_, ?_, m, Q', inner, hRF.injective.comp hQi,
    Q.hasSimplicialEdges_affineImage hQ F.toAffineMap hRF.injective, ?_, ?_, ?_⟩
  · intro c hc t ht
    have h := hFmem _ (hin c hc t ht)
    rwa [hval _ _ (hsigned c hc positive) ht] at h
  · intro c hc t ht hDmem
    apply hout c hc t ht
    have hc' : (if positive then -c else c) ∈ Icc (-1 : ℝ) 1 := by
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals constructor <;> linarith [hc.1, hc.2]
    refine ⟨sigma ((0, if positive then -c else c), t), hDmem, ?_⟩
    rfl
  · rw [hQ'b, hQb, image_image]
    apply image_congr
    intro t ht
    exact hval _ t (by cases positive <;> norm_num) ht
  · rw [hQ'b]
    exact hQdisk.affine_image F hRF.injective.injOn
  · rintro _ ⟨x, hx, rfl⟩
    exact hFmem x (hQinside hx)

end PoincareConjecture.M76
