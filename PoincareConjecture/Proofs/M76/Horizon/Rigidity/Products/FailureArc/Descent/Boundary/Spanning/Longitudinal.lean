import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.TubeRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.OriginalStripDoubleLocus



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

def spanningSourceReverse : P2 →ᴬ[ℝ] P2 :=
  (ContinuousAffineMap.const ℝ P2 1 - (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap

def spanningTubeReverse : C3 →ᴬ[ℝ] C3 :=
  (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.prod
    (ContinuousAffineMap.const ℝ C3 1 - (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap)

theorem spanningSourceReverse_apply (p : P2) : spanningSourceReverse p = (1 - p.1, p.2) := rfl
theorem spanningTubeReverse_apply (z : C3) : spanningTubeReverse z = (z.1, 1 - z.2) := rfl

theorem spanningSourceReverse_involutive : Function.Involutive spanningSourceReverse := by
  intro p
  ext <;> simp [spanningSourceReverse_apply]

theorem spanningTubeReverse_involutive : Function.Involutive spanningTubeReverse := by
  intro z
  exact Prod.ext rfl (by simp [spanningTubeReverse_apply])

theorem spanningSourceReverse_mapsTo : MapsTo spanningSourceReverse source source := by
  intro p hp
  exact ⟨⟨by change 0 ≤ 1 - p.1; linarith [hp.1.2],
    by change 1 - p.1 ≤ 1; linarith [hp.1.1]⟩, hp.2⟩

theorem spanningTubeReverse_mapsTo : MapsTo spanningTubeReverse tube tube := by
  intro z hz
  exact ⟨hz.1, ⟨by change 0 ≤ 1 - z.2; linarith [hz.2.2],
    by change 1 - z.2 ≤ 1; linarith [hz.2.1]⟩⟩

theorem spanningSourceReverse_image : spanningSourceReverse '' source = source :=
  Subset.antisymm (image_subset_iff.mpr spanningSourceReverse_mapsTo)
    (fun p hp ↦ ⟨spanningSourceReverse p, spanningSourceReverse_mapsTo hp,
      spanningSourceReverse_involutive p⟩)

theorem spanningTubeReverse_image : spanningTubeReverse '' tube = tube :=
  Subset.antisymm (image_subset_iff.mpr spanningTubeReverse_mapsTo)
    (fun z hz ↦ ⟨spanningTubeReverse z, spanningTubeReverse_mapsTo hz,
      spanningTubeReverse_involutive z⟩)

theorem spanningSourceReverse_arm_image (u : ℝ) : spanningSourceReverse '' arm u = arm u := by
  have hmaps : MapsTo spanningSourceReverse (arm u) (arm u) := by
    intro p hp
    exact ⟨⟨by change 0 ≤ 1 - p.1; linarith [hp.1.2],
      by change 1 - p.1 ≤ 1; linarith [hp.1.1]⟩, hp.2⟩
  exact Subset.antisymm (image_subset_iff.mpr hmaps)
    (fun p hp ↦ ⟨spanningSourceReverse p, hmaps hp, spanningSourceReverse_involutive p⟩)

theorem spanningSourceReverse_finitePL : FinitePiecewiseAffineOn spanningSourceReverse source := by
  have hb := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hb
  exact ⟨K, hK, hKs, K.affineOnFaces_affine spanningSourceReverse⟩

theorem spanningTubeReverse_finitePL : FinitePiecewiseAffineOn spanningTubeReverse tube := by
  obtain ⟨K, hK, hKs, _⟩ := tubeTransverseContraction_finitePL 1
  exact ⟨K, hK, hKs, K.affineOnFaces_affine spanningTubeReverse⟩

theorem spanningReverse_sheet (i : Bool) (p : P2) :
    originalStripSheet i (spanningSourceReverse p) = spanningTubeReverse (originalStripSheet i p) :=
  rfl

theorem spanningTubeReverse_polyhedralPL
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube) :
    PolyhedralPLInCharts e (τ ∘ spanningTubeReverse) tube := by
  obtain ⟨K, hK, hKs, haff⟩ := spanningTubeReverse_finitePL
  simpa only [hKs] using hτ.comp_finitePiecewiseAffineOn K hK
    ⟨K, hK, rfl, haff⟩ (hKs.symm ▸ spanningTubeReverse_mapsTo)

end PoincareConjecture.M76.Dehn
