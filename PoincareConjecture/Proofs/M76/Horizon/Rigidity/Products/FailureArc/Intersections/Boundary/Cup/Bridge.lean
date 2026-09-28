import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.OriginalStripDoubleLocus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.FiniteDisk



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryCup

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

noncomputable def bridgeCoordinates : P2 →ᴬ[ℝ] C3 :=
  (((2 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ P2 1).prod (ContinuousAffineMap.const ℝ P2 1)).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

theorem bridgeCoordinates_apply (p : P2) :
    bridgeCoordinates p = ((2 * p.2 + 1, 1), p.1) := rfl

theorem bridgeCoordinates_mapsTo : MapsTo bridgeCoordinates (halfSource false) tube := by
  intro p hp
  change ((-1 ≤ 2 * p.2 + 1 ∧ 2 * p.2 + 1 ≤ 1) ∧
    (1 : ℝ) ∈ Icc (-1) 1) ∧ p.1 ∈ Icc (0 : ℝ) 1
  refine ⟨⟨⟨?_, ?_⟩, by norm_num⟩, hp.1⟩ <;> linarith [hp.2.1, hp.2.2]

theorem bridgeCoordinates_injective : Function.Injective bridgeCoordinates := by
  intro p q hpq
  have ht := congrArg Prod.snd hpq
  have hu := congrArg (fun z : C3 ↦ z.1.1) hpq
  apply Prod.ext ht
  change 2 * p.2 + 1 = 2 * q.2 + 1 at hu
  linarith

theorem bridgeCoordinates_image :
    bridgeCoordinates '' halfSource false =
      (Icc (-1 : ℝ) 1 ×ˢ {(1 : ℝ)}) ×ˢ Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨(bridgeCoordinates_mapsTo hp).1.1, rfl⟩, hp.1⟩
  · rintro ⟨⟨x, y⟩, t⟩ ⟨⟨hx, hy⟩, ht⟩
    have hy' : y = 1 := hy
    subst y
    refine ⟨(t, (x - 1) / 2), ⟨ht, ?_⟩, ?_⟩
    · change -1 ≤ (x - 1) / 2 ∧ (x - 1) / 2 ≤ 0
      constructor <;> linarith [hx.1, hx.2]
    · rw [bridgeCoordinates_apply]
      congr 2
      ring

theorem bridgeCoordinates_finitePL :
    FinitePiecewiseAffineOn bridgeCoordinates (halfSource false) := by
  have hrect := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hrect
  exact ⟨K, hK, hKs, K.affineOnFaces_affine bridgeCoordinates⟩

theorem original_bridge_properties
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {τ : C3 → X}
    (hτ : PolyhedralPLInCharts e τ tube) (hτi : InjOn τ tube)
    {A B R : Set X}
    (hA : ∀ z ∈ tube, τ z ∈ A ↔ z.1.2 = z.1.1)
    (hB : ∀ z ∈ tube, τ z ∈ B ↔ z.1.2 = -z.1.1)
    (hR : MapsTo τ tube R)
    (hfront : ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) :
    PolyhedralPLInCharts e (τ ∘ bridgeCoordinates) (halfSource false) ∧
      InjOn (τ ∘ bridgeCoordinates) (halfSource false) ∧
      MapsTo (τ ∘ bridgeCoordinates) (halfSource false) R ∧
      (∀ p ∈ halfSource false, (τ ∘ bridgeCoordinates) p ∈ A ↔ p.2 = 0) ∧
      (∀ p ∈ halfSource false, (τ ∘ bridgeCoordinates) p ∈ B ↔ p.2 = -1) ∧
      (∀ p ∈ halfSource false, (τ ∘ bridgeCoordinates) p ∈ frontier R ↔ p.1 = 0 ∨ p.1 = 1) ∧
      (τ ∘ bridgeCoordinates) '' halfSource false =
        τ '' ((Icc (-1 : ℝ) 1 ×ˢ {(1 : ℝ)}) ×ˢ Icc (0 : ℝ) 1) := by
  have hPL : PolyhedralPLInCharts e (τ ∘ bridgeCoordinates) (halfSource false) := by
    obtain ⟨K, hK, hKs, hfaces⟩ := bridgeCoordinates_finitePL
    rw [← hKs]
    exact hτ.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hfaces⟩
      (fun p hp ↦ bridgeCoordinates_mapsTo (hKs.subset hp))
  refine ⟨hPL, hτi.comp bridgeCoordinates_injective.injOn bridgeCoordinates_mapsTo,
    hR.comp bridgeCoordinates_mapsTo, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [Function.comp_apply, hA _ (bridgeCoordinates_mapsTo hp)]
    change 1 = 2 * p.2 + 1 ↔ p.2 = 0
    constructor <;> intro h <;> linarith
  · intro p hp
    rw [Function.comp_apply, hB _ (bridgeCoordinates_mapsTo hp)]
    change 1 = -(2 * p.2 + 1) ↔ p.2 = -1
    constructor <;> intro h <;> linarith
  · intro p hp
    exact hfront _ (bridgeCoordinates_mapsTo hp)
  · rw [image_comp, bridgeCoordinates_image]

end PoincareConjecture.M76.Dehn.Annuli.BoundaryCup
