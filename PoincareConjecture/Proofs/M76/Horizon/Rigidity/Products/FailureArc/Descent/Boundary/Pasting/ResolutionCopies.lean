import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.Fibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionTubeFibers



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

def squareStripCoordinates : P2 →ᴬ[ℝ] P2 :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap.prod
    ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ P2 1)

theorem squareStripCoordinates_apply (z : P2) :
    squareStripCoordinates z = (z.2, 2 * z.1 - 1) := rfl

theorem squareStripCoordinates_mapsTo : MapsTo squareStripCoordinates Sq source := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  change -1 ≤ 2 * z.1 - 1 ∧ 2 * z.1 - 1 ≤ 1
  constructor <;> linarith [hz.1.1, hz.1.2]

theorem squareStripCoordinates_injective : Function.Injective squareStripCoordinates := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change x.2 = y.2 at h₁
  change 2 * x.1 - 1 = 2 * y.1 - 1 at h₂
  exact Prod.ext (by linarith) h₁

theorem squareStripCoordinates_finitePL : FinitePiecewiseAffineOn squareStripCoordinates Sq := by
  have hrect := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, c, hc, _⟩ := hrect
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
  exact hKs ▸ (K.affineOnFaces_affine squareStripCoordinates).finitePiecewiseAffineOn hK

noncomputable def resolvingSquare (positive : Bool) : P2 → C3 :=
  strip (1 / 4) positive ∘ squareStripCoordinates

theorem resolvingSquare_finitePL (positive : Bool) :
    FinitePiecewiseAffineOn (resolvingSquare positive) Sq :=
  (finitePiecewiseAffineOn_maps (1 / 4) positive).1.comp
    squareStripCoordinates_finitePL squareStripCoordinates_mapsTo

theorem resolvingSquare_mapsTo (positive : Bool) : MapsTo (resolvingSquare positive) Sq tube :=
  (mapsTo_tube (show (1 / 4 : ℝ) ≤ 1 by norm_num) positive).1.comp
    squareStripCoordinates_mapsTo

theorem resolvingSquare_left (positive : Bool) (t : I) :
    resolvingSquare positive (0, t) = strip 0 positive (t, -1) := by
  change strip (1 / 4) positive (t, 2 * 0 - 1) = _
  norm_num only
  exact (eq_zero_of_outer positive (t, -1) (by norm_num : (1 / 4 : ℝ) ≤ |(-1 : ℝ)|)).1

theorem resolvingSquare_right (positive : Bool) (t : I) :
    resolvingSquare positive (1, t) = strip 0 positive (t, 1) := by
  change strip (1 / 4) positive (t, 2 * 1 - 1) = _
  norm_num only
  exact (eq_zero_of_outer positive (t, 1) (by norm_num : (1 / 4 : ℝ) ≤ |(1 : ℝ)|)).1

theorem resolvingSquare_target_injective {X : Type*} {τ : C3 → X}
    (hτ : InjOn τ tube) (positive : Bool) : InjOn (τ ∘ resolvingSquare positive) Sq := by
  intro x hx y hy h
  apply squareStripCoordinates_injective
  exact (embedding_maps (1 / 4) positive).1.injective
    (hτ (resolvingSquare_mapsTo positive hx) (resolvingSquare_mapsTo positive hy) h)

theorem exists_resolving_annulus_with_copies
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {d : P2 → X} {τ : C3 → X}
    (hd : PolyhedralPLInCharts e d Sq) (hτ : PolyhedralPLInCharts e τ tube)
    (positive : Bool)
    (hleft : ∀ t : I, d (0, t) = τ (strip 0 positive (t, -1)))
    (hright : ∀ t : I, d (1, t) = τ (strip 0 positive (t, 1))) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g (squareAnnulus 8 1) ∧
      Nonempty (AnnulusSquareCopies ![d, τ ∘ resolvingSquare positive] g) := by
  have hq : PolyhedralPLInCharts e (τ ∘ resolvingSquare positive) Sq := by
    obtain ⟨K, hK, hKs, hAff⟩ := resolvingSquare_finitePL positive
    simpa only [hKs] using hτ.comp_finitePiecewiseAffineOn K hK
      ⟨K, hK, rfl, hAff⟩ (hKs.symm ▸ resolvingSquare_mapsTo positive)
  apply exists_standard_annulus_map_with_copies hcompat ![d, τ ∘ resolvingSquare positive]
  · intro j
    fin_cases j <;> assumption
  · intro t
    change d (0, t) = τ (resolvingSquare positive (0, t))
    rw [resolvingSquare_left]
    exact hleft t
  · intro t
    change d (1, t) = τ (resolvingSquare positive (1, t))
    rw [resolvingSquare_right]
    exact hright t

theorem resolving_copies_double_points
    {X : Type*} {d g : P2 → X} {τ : C3 → X} (positive : Bool)
    (C : AnnulusSquareCopies ![d, τ ∘ resolvingSquare positive] g)
    (hτ : InjOn τ tube)
    (hpre : ∀ z : Sq, d z ∈ τ '' tube ↔ (z : P2).1 = 0 ∨ (z : P2).1 = 1)
    (hleft : ∀ t : I, d (0, t) = τ (strip 0 positive (t, -1)))
    (hright : ∀ t : I, d (1, t) = τ (strip 0 positive (t, 1))) :
    {x : P2 | x ∈ squareAnnulus 8 1 ∧
      ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
    (fun z : Sq ↦ (C.chart 0 z : P2)) ''
      {u : Sq | ∃ v : Sq, v ≠ u ∧ d v = d u} := by
  apply C.double_points_eq_retained hpre
  · intro z hz
    exact ⟨resolvingSquare positive z, resolvingSquare_mapsTo positive hz, rfl⟩
  · exact resolvingSquare_target_injective hτ positive
  · intro t
    change d (0, t) = τ (resolvingSquare positive (0, t))
    rw [resolvingSquare_left]
    exact hleft t
  · intro t
    change d (1, t) = τ (resolvingSquare positive (1, t))
    rw [resolvingSquare_right]
    exact hright t

end PoincareConjecture.M76.Dehn
