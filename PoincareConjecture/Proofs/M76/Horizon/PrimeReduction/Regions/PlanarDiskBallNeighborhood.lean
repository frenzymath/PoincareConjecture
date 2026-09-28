import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.PlanarCircleOuterDisk
import PoincareConjecture.Proofs.M76.PrimeReduction.CompactFaceNormalBall

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_normal_ball_of_planar_disk_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h3 : Module.finrank ℝ E = 3)
    {D Dout rimout : Set P2} (hDout : IsFinitePLBallPair P2 Dout rimout)
    (hDint : D ⊆ interior Dout) (F : P2 →ᴬ[ℝ] E) (hFi : Function.Injective F)
    {O : Set E} (hO : IsOpen O) (hFO : F '' Dout ⊆ O) :
    ∃ B bd : Set E, IsFinitePLBallPair P3 B bd ∧ F '' D ⊆ interior B ∧ B ⊆ O := by
  obtain ⟨T, hzero, _, _⟩ := F.exists_normal_extension hFi h3
  obtain ⟨ε, hε, hproduct⟩ := hDout.isCompact.exists_closed_normal_interval
    (hO.preimage T.continuous) (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have ht0 : t = 0 := ht
      change T (x, t) ∈ O
      rw [ht0, hzero]
      exact hFO ⟨x, hx, rfl⟩)
  let B := T '' (Dout ×ˢ Icc (-ε) ε)
  let bd := T '' ((rimout ×ˢ Icc (-ε) ε) ∪ (Dout ×ˢ {-ε, ε}))
  have hprod := hDout.prod (isFinitePLBallPair_Icc (show -ε < ε by linarith))
  have hball : IsFinitePLBallPair P3 B bd :=
    hprod.affine_image T.toContinuousAffineMap T.injective.injOn
  refine ⟨B, bd, hball, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxpair : x ∈ Dout \ rimout := by
      rw [← hDout.interior_eq_sdiff_of_finrank_eq rfl]
      exact hDint hx
    apply hball.sdiff_subset_interior_of_finrank_eq
      (by simp [Module.finrank_prod, h3])
    refine ⟨⟨(x, 0), ⟨hxpair.1, by constructor <;> linarith⟩, hzero x⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    have hzx' : z = (x, 0) := T.injective (hzx.trans (hzero x).symm)
    subst z
    rcases hz with hz | hz
    · exact hxpair.2 hz.1
    · have ht : (0 : ℝ) = -ε ∨ (0 : ℝ) = ε := by simpa using hz.2
      rcases ht with ht | ht <;> linarith
  · rintro _ ⟨z, hz, rfl⟩
    exact hproduct hz

theorem exists_planar_circle_disk_ball_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h3 : Module.finrank ℝ E = 3)
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
      f x ∈ P.boundary ℝ ↔ x.1 = 0)
    (haxisImage : (fun t : ℝ => f (0, t)) '' Icc 0 β = P.boundary ℝ)
    (F : P2 →ᴬ[ℝ] E) (hFi : Function.Injective F)
    {O : Set E} (hO : IsOpen O)
    (hFO : F '' (D ∪ f '' (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β)) ⊆ O) :
    ∃ B bd : Set E, IsFinitePLBallPair P3 B bd ∧ F '' D ⊆ interior B ∧ B ⊆ O := by
  obtain ⟨_, Dout, rimout, hDout, hDint, hDsub, _⟩ :=
    exists_outer_disk_of_planar_circle_strip P hP hPi hD hβ f hf hfib haxis haxisImage
  exact exists_normal_ball_of_planar_disk_interior h3 hDout hDint F hFi hO
    ((image_mono hDsub).trans hFO)

theorem exists_ball_neighborhood_of_identity_circle_tube
    {n : ℕ} (L : Polygon V3 (n + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) {D T : Set V3}
    (hD : IsFinitePLBallPair P2 D (L.boundary ℝ)) (hDT : D ⊆ T)
    (F : P2 →ᴬ[ℝ] V3) (R : V3 →ᴬ[ℝ] P2)
    (hRF : Function.LeftInverse R F) (hFR : EqOn (F ∘ R) id T)
    {β : ℝ} (hβ : 0 < β) (sigma : P3 → V3)
    (hSigma : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc 0 β))
    (htriangle : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ T ↔ x.1 ∈ signedTubeSheet 0)
    (haxis : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x ∈ L.boundary ℝ ↔ x.1 = (0, 0))
    (haxisImage : (fun t : ℝ => sigma ((0, 0), t)) '' Icc 0 β = L.boundary ℝ)
    (hfib : ∀ x ∈ signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ signedTubeDiamond ×ˢ Icc 0 β,
      sigma x = sigma y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β)))
    {V : Set V3} (hV : IsOpen V) (hDV : D ⊆ V)
    (hSigmaV : sigma '' (signedTubeDiamond ×ˢ Icc 0 β) ⊆ V) :
    ∃ B bd : Set V3, IsFinitePLBallPair P3 B bd ∧ D ⊆ interior B ∧ B ⊆ V := by
  have hRi : InjOn R T := by
    intro x hx y hy heq
    exact (hFR hx).symm.trans ((congrArg F heq).trans (hFR hy))
  have hLT : L.boundary ℝ ⊆ T := hD.1.trans hDT
  let P := L.affineImage R.toAffineMap
  have hPb : P.boundary ℝ = R '' L.boundary ℝ := L.affineImage_boundary R.toAffineMap
  obtain ⟨hPi, hP, _⟩ := L.affineImage_of_leftInvOn hL hLi R.toAffineMap
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
  have hstripImage : (fun t : ℝ => f (0, t)) '' Icc 0 β = P.boundary ℝ := by
    rw [hPb, ← haxisImage, image_image]
    rfl
  have hFD : F '' (R '' D) = D := by
    rw [image_image]
    calc
      _ = id '' D := image_congr (hFR.mono hDT)
      _ = D := image_id _
  have hFO : F '' ((R '' D) ∪ f '' (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β)) ⊆ V := by
    rw [image_union, hFD]
    refine union_subset hDV ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change F (R (sigma (signedSheetStripMap 0 x))) ∈ V
    rw [show F (R (sigma (signedSheetStripMap 0 x))) =
      sigma (signedSheetStripMap 0 x) from hFR (hstrip x hx)]
    exact hSigmaV ⟨signedSheetStripMap 0 x, signedSheetStripMap_mem 0 hx, rfl⟩
  obtain ⟨B, bd, hB, hDB, hBV⟩ := exists_planar_circle_disk_ball_neighborhood
    (by simp : Module.finrank ℝ V3 = 3) P hP hPi hDp hβ f hf hstripfib
    hstripAxis hstripImage F hRF.injective hV hFO
  exact ⟨B, bd, hB, hFD ▸ hDB, hBV⟩

end PoincareConjecture.M76
