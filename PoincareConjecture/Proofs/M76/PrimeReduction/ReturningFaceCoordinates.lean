import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation
import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskRegions
import Mathlib.Analysis.Convex.SimplicialComplex.Basic










set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in



theorem exists_returning_face_coordinates
    {K : SimplicialComplex ℝ E} {v0 v1 v2 : E}
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2)
    (hs : ({v0, v1, v2} : Finset E) ∈ K.faces) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ)),
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (affineSpan ℝ ({v0, v1, v2} : Set E)) ∧
      F (0, 0) = v0 ∧ F (1, 0) = v1 ∧ F (0, 1) = v2 ∧
      F '' convexHull ℝ (range rightTriangle) = convexHull ℝ ({v0, v1, v2} : Set E) ∧
      F '' segment ℝ (0, 0) (1, 0) = convexHull ℝ ({v0, v1} : Set E) ∧
      R '' convexHull ℝ ({v0, v1, v2} : Set E) = convexHull ℝ (range rightTriangle) ∧
      (∀ z, F z ∈ convexHull ℝ ({v0, v1} : Set E) → z.2 = 0) := by
  classical
  let f : E → ℝ × ℝ := fun v => if v = v1 then (1, 0) else if v = v2 then (0, 1) else (0, 0)
  obtain ⟨R, hR⟩ := (K.indep hs).exists_continuousAffineMap_eqOn f
  have hR0 : R v0 = (0, 0) := by
    simpa [f, h01, h02] using hR (by simp : v0 ∈ ({v0, v1, v2} : Finset E))
  have hR1 : R v1 = (1, 0) := by
    simpa [f] using hR (by simp : v1 ∈ ({v0, v1, v2} : Finset E))
  have hR2 : R v2 = (0, 1) := by
    simpa [f, h12.symm] using hR (by simp : v2 ∈ ({v0, v1, v2} : Finset E))
  let F : (ℝ × ℝ) →ᴬ[ℝ] E :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (v1 - v0) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (v2 - v0)).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) v0
  have hF0 : F (0, 0) = v0 := by simp [F]
  have hF1 : F (1, 0) = v1 := by simp [F]
  have hF2 : F (0, 1) = v2 := by simp [F]
  have hspan : affineSpan ℝ (range rightTriangle) = ⊤ :=
    independent_rightTriangle.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [Module.finrank_prod])
  have hRF : R.toAffineMap.comp F.toAffineMap = AffineMap.id ℝ (ℝ × ℝ) := by
    apply AffineMap.ext_on hspan
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change R (F (0, 0)) = (0, 0)
      rw [hF0, hR0]
    · change R (F (1, 0)) = (1, 0)
      rw [hF1, hR1]
    · change R (F (0, 1)) = (0, 1)
      rw [hF2, hR2]
  have hleft : Function.LeftInverse R F := fun z => congrArg (fun a => a z) hRF
  have hFR : EqOn (F ∘ R) id (affineSpan ℝ ({v0, v1, v2} : Set E)) := by
    apply AffineMap.eqOn_affineSpan (f := F.toAffineMap.comp R.toAffineMap)
      (g := AffineMap.id ℝ E)
    intro x hx
    change F (R x) = x
    rcases hx with h | h | h
    · rw [h, hR0, hF0]
    · rw [h, hR1, hF1]
    · rw [h, hR2, hF2]
  have hverts : F '' range rightTriangle = ({v0, v1, v2} : Set E) := by
    rw [← range_comp]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl hF0
      · exact Or.inr (Or.inl hF1)
      · exact Or.inr (Or.inr hF2)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, hF0⟩
      · exact ⟨1, hF1⟩
      · exact ⟨2, hF2⟩
  have hface : F '' convexHull ℝ (range rightTriangle) =
      convexHull ℝ ({v0, v1, v2} : Set E) := by
    exact (F.toAffineMap.image_convexHull _).trans (congrArg (convexHull ℝ) hverts)
  have hedge : F '' segment ℝ (0, 0) (1, 0) =
      convexHull ℝ ({v0, v1} : Set E) := by
    have himage := F.toAffineMap.image_convexHull ({(0, 0), (1, 0)} : Set (ℝ × ℝ))
    rw [convexHull_pair] at himage
    refine himage.trans ?_
    change convexHull ℝ (F '' ({(0, 0), (1, 0)} : Set (ℝ × ℝ))) = _
    simp only [image_insert_eq, image_singleton, hF0, hF1]
  have hRface : R '' convexHull ℝ ({v0, v1, v2} : Set E) =
      convexHull ℝ (range rightTriangle) := by
    rw [← hface, ← image_comp]
    have hfun : R ∘ F = id := funext hleft
    rw [hfun, image_id]
  refine ⟨F, R, hleft, hFR, hF0, hF1, hF2, hface, hedge, hRface, ?_⟩
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hedge.symm.subset hz
  have hwz' : w = z := hleft.injective hwz
  subst w
  rcases hw with ⟨a, b, _, _, _, heq⟩
  have h := congrArg Prod.snd heq
  simpa using h.symm

end Geometry.SimplicialComplex
