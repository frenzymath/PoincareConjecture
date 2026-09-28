import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "D" => Dehn.signedTubeDiamond




theorem exists_planar_signed_tube_ribbon
    {T triangle sphere : Set V3}
    (tube : ↥(D ×ˢ I) ≃ₜ T) (htube : tube.IsFinitePL)
    (htriangle : ∀ x : ↥(D ×ˢ I),
      (x : P3).1 ∈ Dehn.signedTubeSheet 0 ↔ (tube x : V3) ∈ triangle)
    (hsphere : ∀ x : ↥(D ×ˢ I),
      (x : P3).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ sphere)
    (R : V3 →ᴬ[ℝ] P2) (F : P2 → V3) (hFR : EqOn (F ∘ R) id triangle)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ f : P2 → P2,
      FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ I) ∧
      InjOn f (Icc (-r) r ×ˢ I) ∧
      MapsTo f (Icc (-r) r ×ˢ I) (R '' triangle) ∧
      (∀ (c : Icc (-r) r) (t : I),
        f (c, t) = R (tube ⟨((0, c), t),
          (Dehn.signedTubeDiamond_coordinate_iff (0, c)).mpr
            (by simpa using (abs_le.mpr c.property).trans hr1), t.property⟩ : V3)) ∧
      (∀ z ∈ Icc (-r) r ×ˢ I,
        f z ∈ R '' (triangle ∩ sphere) ↔ z.1 = 0) ∧
      (∀ t ∈ I, ContinuousOn (fun c => f (c, t)) (Icc (-r) r) ∧
        InjOn (fun c => f (c, t)) (Icc (-r) r)) ∧
      (∀ z ∈ Ioo (-r) r ×ˢ Ioo (0 : ℝ) 1,
        f z ∈ interior (R '' triangle)) ∧
      (∀ c ∈ Icc (-r) r,
        FinitePiecewiseAffineOn (fun t => f (c, t)) I ∧
        InjOn (fun t => f (c, t)) I ∧
        IsFinitePLBallPair ℝ ((fun t => f (c, t)) '' I) {f (c, 0), f (c, 1)} ∧
        (c ≠ 0 → Disjoint ((fun t => f (c, t)) '' I) (R '' (triangle ∩ sphere)))) := by
  classical
  have hRi : InjOn R triangle := by
    intro x hx y hy hxy
    exact (hFR hx).symm.trans ((congrArg F hxy).trans (hFR hy))
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hrect := (isFinitePLBallPair_Icc (show -r < r by linarith)).prod hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hrect
  let sheet : P2 →ᴬ[ℝ] P3 :=
    ((ContinuousAffineMap.const ℝ P2 (0 : ℝ)).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hsheetPL : FinitePiecewiseAffineOn sheet (Icc (-r) r ×ˢ I) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine sheet⟩
  have hsheet (z : P2) (hz : z ∈ Icc (-r) r ×ˢ I) : sheet z ∈ D ×ˢ I :=
    ⟨(Dehn.signedTubeDiamond_coordinate_iff (0, z.1)).mpr
      (by simpa using (abs_le.mpr hz.1).trans hr1), hz.2⟩
  obtain ⟨old, hold, hval⟩ := htube
  let g : P2 → V3 := old ∘ sheet
  have hg : FinitePiecewiseAffineOn g (Icc (-r) r ×ˢ I) :=
    hold.comp hsheetPL (fun z hz => hsheet z hz)
  have hgval (z : P2) (hz : z ∈ Icc (-r) r ×ˢ I) :
      g z = (tube ⟨sheet z, hsheet z hz⟩ : V3) :=
    (hval ⟨sheet z, hsheet z hz⟩).symm
  have hgT (z : P2) (hz : z ∈ Icc (-r) r ×ˢ I) : g z ∈ triangle := by
    rw [hgval z hz]
    apply (htriangle _).mp
    exact (Dehn.signedTubeSheet_coordinate_iff (0, z.1) (hsheet z hz).1 0).mpr (by simp)
  let f : P2 → P2 := R ∘ g
  have hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ I) := by
    obtain ⟨N, hN, hNs, hgN⟩ := hg
    exact ⟨N, hN, hNs, hgN.postcomp R⟩
  have hfi : InjOn f (Icc (-r) r ×ˢ I) := by
    intro x hx y hy hxy
    have hgeq : g x = g y := hRi (hgT x hx) (hgT y hy) hxy
    have hteq : tube ⟨sheet x, hsheet x hx⟩ = tube ⟨sheet y, hsheet y hy⟩ := by
      apply Subtype.ext
      exact (hgval x hx).symm.trans (hgeq.trans (hgval y hy))
    have hseq := congrArg Subtype.val (tube.injective hteq)
    exact Prod.ext (congrArg (fun z : P3 => z.1.2) hseq)
      (congrArg (fun z : P3 => z.2) hseq)
  have hmap : MapsTo f (Icc (-r) r ×ˢ I) (R '' triangle) :=
    fun z hz => ⟨g z, hgT z hz, rfl⟩
  have hs (z : P2) (hz : z ∈ Icc (-r) r ×ˢ I) :
      f z ∈ R '' (triangle ∩ sphere) ↔ z.1 = 0 := by
    have hgS : g z ∈ sphere ↔ z.1 = 0 := by
      rw [hgval z hz, ← hsphere]
      exact Dehn.signedTubeSheet_coordinate_iff (0, z.1) (hsheet z hz).1 1
    constructor
    · rintro ⟨y, hy, heq⟩
      have he : y = g z := hRi hy.1 (hgT z hz) heq
      exact hgS.mp (he ▸ hy.2)
    · intro h
      exact ⟨g z, ⟨hgT z hz, hgS.mpr h⟩, rfl⟩
  refine ⟨f, hf, hfi, hmap, ?_, hs, ?_, ?_, ?_⟩
  · intro c t
    exact congrArg R (hgval (c, t) ⟨c.property, t.property⟩)
  · intro t ht
    refine ⟨hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun c hc => ⟨hc, ht⟩), ?_⟩
    intro c hc d hd heq
    exact congrArg Prod.fst (hfi ⟨hc, ht⟩ ⟨hd, ht⟩ heq)
  · intro z hz
    apply interior_mono (show f '' (Icc (-r) r ×ˢ I) ⊆ R '' triangle from
      image_subset_iff.mpr hmap)
    apply hf.mem_interior_image rfl hfi
    simpa only [interior_prod_eq, interior_Icc] using hz
  · intro c hc
    let line : ℝ →ᴬ[ℝ] P2 :=
      (ContinuousAffineMap.const ℝ ℝ c).prod (ContinuousAffineMap.id ℝ ℝ)
    have hcopy := hI
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ := hcopy
    have hline : FinitePiecewiseAffineOn line I :=
      ⟨L, hL, hLs, L.affineOnFaces_affine line⟩
    have hfc : FinitePiecewiseAffineOn (fun t => f (c, t)) I :=
      hf.comp hline (fun t ht => ⟨hc, ht⟩)
    have hci : InjOn (fun t => f (c, t)) I := by
      intro t ht u hu heq
      exact congrArg Prod.snd (hfi ⟨hc, ht⟩ ⟨hc, hu⟩ heq)
    refine ⟨hfc, hci, ?_, ?_⟩
    · simpa only [image_pair] using hI.image hfc hci
    · intro hc0
      apply disjoint_left.mpr
      rintro _ ⟨t, ht, rfl⟩ hS
      exact hc0 ((hs (c, t) ⟨hc, ht⟩).mp hS)

end PoincareConjecture.M76
