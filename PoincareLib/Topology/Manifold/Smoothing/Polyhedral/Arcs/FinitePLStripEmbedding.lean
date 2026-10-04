import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.HeightPreservingPLStrip
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FiniteAffineHalfspaceGeometry
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FinitePLCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.PlanarSegmentHeight

/-!
# Finite PL embeddings of regular strips

The square has an exact finite triangulation. Positive-width
strip coordinates followed by an affine embedding therefore
give a finite PL homeomorphism onto the geometric strip image.
See Alexander 1924, pp. 6--8, Hudson 1969, pp. 12--19 and M76
derivation 159.
-/

set_option autoImplicit false

open Set Geometry

namespace PLStrip

/-- The closed parameter square for a regular surface strip.
See M76 derivation 159. -/
def square : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- The parameter square has a finite triangulation of its
exact carrier. See Hudson pp. 12--14 and derivation 159. -/
theorem exists_finite_triangulation_square :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), K.faces.Finite ∧ K.space = square := by
  classical
  let X : (ℝ × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).toAffineMap
  let Y : (ℝ × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ ℝ ℝ).toAffineMap
  let C : (ℝ × ℝ) →ᵃ[ℝ] ℝ := AffineMap.const ℝ (ℝ × ℝ) 1
  apply (isCompact_Icc.prod isCompact_Icc).exists_finite_triangulation_of_halfspaces
    {-X, X - C, -Y, Y - C}
  ext q
  simp only [mem_prod, mem_Icc, mem_ofPred_eq, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  change (0 ≤ q.1 ∧ q.1 ≤ 1) ∧ (0 ≤ q.2 ∧ q.2 ≤ 1) ↔
    -q.1 ≤ 0 ∧ q.1 - 1 ≤ 0 ∧ -q.2 ≤ 0 ∧ q.2 - 1 ≤ 0
  simp only [neg_nonpos, sub_nonpos]
  tauto

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every horizontal width of the regular strip is positive,
including both endpoint levels. See M76 derivation 159. -/
theorem strip_width_pos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ Icc 0 1) :
    0 < a * t + b * (1 - t) := by
  by_cases ht0 : t = 0
  · simpa [ht0] using hb
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (lt_of_le_of_ne ht.1 (Ne.symm ht0)))
      (mul_nonneg hb.le (sub_nonneg.mpr ht.2))

/-- The exact affine strip image is the union of its horizontal
segments. This retains their ordered affine endpoints.
See Alexander pp. 6--8 and M76 derivation 159. -/
theorem affine_strip_image {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (Q : (ℝ × ℝ) →ᴬ[ℝ] E) :
    (Q ∘ stripMap a b) '' square =
      {x | ∃ t ∈ Icc (0 : ℝ) 1,
        x ∈ segment ℝ (Q (0, t)) (Q (a * t + b * (1 - t), t))} := by
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) :
      segment ℝ (0, t) (a * t + b * (1 - t), t) =
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ a * t + b * (1 - t) ∧ q.2 = t} := by
    ext q
    rw [PlanarSegment.mem_segment_iff (strip_width_pos ha hb ht).ne]
    simp [uIcc_of_le (strip_width_pos ha hb ht).le, PlanarSegment.height, and_assoc]
  have him (t : ℝ) :
      Q '' segment ℝ (0, t) (a * t + b * (1 - t), t) =
        segment ℝ (Q (0, t)) (Q (a * t + b * (1 - t), t)) :=
    image_segment ℝ Q.toAffineMap _ _
  change (fun x => Q (stripMap a b x)) '' square = _
  rw [← image_image Q (stripMap a b), square, stripMap_image_square ha hb]
  ext x
  constructor
  · rintro ⟨q, ⟨hqt, hqx, hqw⟩, rfl⟩
    refine ⟨q.2, hqt, ?_⟩
    rw [← him]
    exact ⟨q, (hseg q.2 hqt).symm ▸ And.intro hqx (And.intro hqw rfl), rfl⟩
  · rintro ⟨t, ht, hx⟩
    rw [← him] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [hseg t ht] at hq
    exact ⟨q, ⟨hq.2.2.symm ▸ ht, hq.1, hq.2.2.symm ▸ hq.2.1⟩, rfl⟩

/-- Affine embeddings of the trapezoid yield finite PL strip
homeomorphisms with the displayed formula on the whole square.
See Alexander pp. 6--8 and M76 derivation 159. -/
theorem exists_affine_strip_homeomorph {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (Q : (ℝ × ℝ) →ᴬ[ℝ] E) (hQ : Function.Injective Q) :
    ∃ e : square ≃ₜ (Q ∘ stripMap a b) '' square, e.IsFinitePL ∧
      ∀ p : square, (e p : E) = Q (stripMap a b p) := by
  obtain ⟨K, hK, hspace⟩ := exists_finite_triangulation_square
  have hPL : FinitePiecewiseAffineOn (stripMap a b) square :=
    hspace ▸ finitePiecewiseAffineOn_stripMap a b K hK
  exact (hPL.postcomp Q).exists_homeomorph_image
    (hQ.comp (stripHomeomorph ha hb).injective).injOn

end PLStrip
