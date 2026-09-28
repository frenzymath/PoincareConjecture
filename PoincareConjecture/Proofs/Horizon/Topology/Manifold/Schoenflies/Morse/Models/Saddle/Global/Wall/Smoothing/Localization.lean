import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Profile
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Region
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Corner.Local

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem monotone_profileX {ρ : Real → Real} (hρ : LipschitzWith 1 ρ) :
    Monotone (profileX ρ) := by
  intro s t hst
  have h := hρ.dist_le_mul t s
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_of_nonneg (sub_nonneg.mpr hst)] at h
  have hle := (le_abs_self (ρ t - ρ s)).trans h
  dsimp [profileX]
  linarith

def edgeNeighborhood (δ : Real) : Set E3 :=
  {p | -δ < p 0 ∧ p 2 - (p 1)^2 < δ}

theorem isOpen_edgeNeighborhood (δ : Real) : IsOpen (edgeNeighborhood δ) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := Real) 0).continuous
  · exact isOpen_lt
      ((EuclideanSpace.proj (𝕜 := Real) 2).continuous.sub
        ((EuclideanSpace.proj (𝕜 := Real) 1).continuous.pow 2)) continuous_const

theorem roundedRegion_subset_leftBody
    (H : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    {ρ : Real → Real} (hbound : ∀ s, |s| ≤ ρ s)
    (hH : ∀ s, H s = profileHeight ρ s) :
    roundedRegion H (profileX ρ) ⊆ Corner.leftBody := by
  intro p hp
  let s := H.symm (p 2 - (p 1)^2)
  have hx : profileX ρ s ≤ 0 := by
    dsimp [profileX]
    linarith [(le_abs_self s).trans (hbound s)]
  have hw : 0 ≤ profileW ρ s := by
    dsimp [profileW]
    linarith [(neg_le_abs s).trans (hbound s)]
  have hh : profileHeight ρ s = p 2 - (p 1)^2 := by
    rw [← hH]
    exact H.apply_symm_apply _
  change p 0 ≤ profileX ρ s at hp
  refine ⟨hp.trans hx, ?_⟩
  dsimp [profileHeight] at hh
  nlinarith [sq_nonneg (p 0 - profileX ρ s)]

theorem roundedRegion_sdiff_edgeNeighborhood
    (H : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    {ρ : Real → Real} {δ : Real} (hδ : 0 < δ)
    (hbound : ∀ s, |s| ≤ ρ s) (hLip : LipschitzWith 1 ρ)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hH : ∀ s, H s = profileHeight ρ s) (hmono : StrictMono H) :
    roundedRegion H (profileX ρ) \ edgeNeighborhood δ =
      Corner.leftBody \ edgeNeighborhood δ := by
  apply Subset.antisymm
  · exact sdiff_subset_sdiff_left (roundedRegion_subset_leftBody H hbound hH)
  · rintro p ⟨hp, hpU⟩
    refine ⟨?_, hpU⟩
    let s := H.symm (p 2 - (p 1)^2)
    have hs : H s = p 2 - (p 1)^2 := H.apply_symm_apply _
    change p 0 ≤ profileX ρ s
    change ¬ (-δ < p 0 ∧ p 2 - (p 1)^2 < δ) at hpU
    by_cases hx : p 0 ≤ -δ
    · have hx0 : p 0 ≤ 0 := hx.trans (by linarith)
      have hρx : ρ (p 0) = -(p 0) := by
        rw [htail _ (by rw [abs_of_nonpos hx0]; linarith), abs_of_nonpos hx0]
      have hXx : profileX ρ (p 0) = p 0 := by
        dsimp [profileX]
        rw [hρx]
        ring
      have hHx : H (p 0) = -(p 0)^2 := by
        rw [hH]
        dsimp [profileHeight, profileW, profileX]
        rw [hρx]
        ring
      have hxs : p 0 ≤ s := hmono.le_iff_le.mp (by rw [hHx, hs]; linarith [hp.2])
      simpa [hXx] using monotone_profileX hLip hxs
    · have hq : δ ≤ p 2 - (p 1)^2 :=
        le_of_not_gt (fun hq => hpU ⟨lt_of_not_ge hx, hq⟩)
      have hρδ : ρ δ = δ := by
        rw [htail _ (le_abs_self δ), abs_of_pos hδ]
      have hHδ : H δ = δ := by
        rw [hH]
        dsimp [profileHeight, profileW, profileX]
        rw [hρδ]
        ring
      have hδs : δ ≤ s := hmono.le_iff_le.mp (by rw [hHδ, hs]; exact hq)
      have hs0 : 0 ≤ s := hδ.le.trans hδs
      have hρs : ρ s = s := by
        rw [htail _ (by rwa [abs_of_nonneg hs0]), abs_of_nonneg hs0]
      simpa [profileX, hρs] using hp.1

theorem exists_rounded_left_side {δ : Real} (hδ : 0 < δ) :
    ∃ (φ : Real → Real) (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      ContDiff Real ∞ φ ∧
      (∀ p, G p 2 = p 2) ∧
      G '' {p : E3 | p 0 ≤ 0} = {p : E3 | p 0 ≤ φ (p 2 - (p 1)^2)} ∧
      {p : E3 | p 0 ≤ φ (p 2 - (p 1)^2)} ⊆ Corner.leftBody ∧
      ({p : E3 | p 0 ≤ φ (p 2 - (p 1)^2)} \ edgeNeighborhood δ =
        Corner.leftBody \ edgeNeighborhood δ) ∧
      (frontier {p : E3 | p 0 ≤ φ (p 2 - (p 1)^2)} \ closure (edgeNeighborhood δ) =
        frontier Corner.leftBody \ closure (edgeNeighborhood δ)) := by
  obtain ⟨ρ, H, hρ, hLip, hbound, _, htail, hH, hmono, _⟩ := exists_smooth_profile hδ
  let φ := fun q => profileX ρ (H.symm q)
  have hx := contDiff_profileX hρ
  have hφ : ContDiff Real ∞ φ := hx.comp H.symm.contDiff
  have hregion := roundedRegion_sdiff_edgeNeighborhood H hδ
    (fun s => (hbound s).1) hLip htail hH hmono
  exact ⟨φ, cornerShear H (profileX ρ) hx, hφ,
    cornerShear_two H (profileX ρ) hx,
    cornerShear_image_halfspace H (profileX ρ) hx,
    roundedRegion_subset_leftBody H (fun s => (hbound s).1) hH,
    hregion, Corner.frontier_sdiff_closure_eq_of_sdiff_eq hregion⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing
