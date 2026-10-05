import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLStripEmbedding

/-!
# Affine source coordinates for a segment times a height interval

The square identifies with the actual slice segment times its
closed height interval by an injective affine map. This supplies
the source of the regular triangle collar. See Alexander 1924,
pp. 6--8, Hudson 1969, pp. 15--19 and M76 derivation 161.
-/

set_option autoImplicit false

open Set Geometry AffineMap

namespace PLStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine square coordinates on an actual segment product.
See M76 derivation 161. -/
noncomputable def segmentProductCoordinates (l r : E) (α β : ℝ) :
    (ℝ × ℝ) →ᴬ[ℝ] (E × ℝ) :=
  (ContinuousAffineMap.lineMap l r).prodMap (ContinuousAffineMap.lineMap α β)

/-- The coordinate values retain both affine parameters.
See M76 derivation 161. -/
theorem segmentProductCoordinates_apply (l r : E) (α β : ℝ) (p : ℝ × ℝ) :
    segmentProductCoordinates l r α β p =
      (lineMap l r p.1, α + (β - α) * p.2) := by
  refine Prod.ext rfl ?_
  change lineMap α β p.2 = α + (β - α) * p.2
  rw [lineMap_apply_ring']
  ring

/-- Distinct segment and height endpoints make the affine
source coordinates injective. See M76 derivation 161. -/
theorem segmentProductCoordinates_injective {l r : E} (hlr : l ≠ r)
    {α β : ℝ} (hαβ : α ≠ β) :
    Function.Injective (segmentProductCoordinates l r α β) := by
  intro p q hpq
  exact Prod.ext ((lineMap_injective ℝ hlr) (congrArg Prod.fst hpq))
    ((lineMap_injective ℝ hαβ) (congrArg Prod.snd hpq))

/-- The square's affine image is the exact segment product,
including both boundary levels. See M76 derivation 161. -/
theorem segmentProductCoordinates_image {l r : E} {α β : ℝ} (hαβ : α ≤ β) :
    segmentProductCoordinates l r α β '' square = segment ℝ l r ×ˢ Icc α β := by
  change Prod.map (lineMap l r) (lineMap α β) ''
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = _
  rw [prodMap_image_prod, ← segment_eq_image_lineMap, ← segment_eq_image_lineMap,
    segment_eq_Icc hαβ]

/-- An affine finite PL square parametrization of the actual
segment times height interval, with its formula retained.
See Hudson pp. 15--19 and M76 derivation 161. -/
theorem exists_segmentProduct_homeomorph {l r : E} (hlr : l ≠ r)
    {α β : ℝ} (hαβ : α < β) :
    ∃ e : square ≃ₜ (segment ℝ l r ×ˢ Icc α β : Set (E × ℝ)),
      e.IsFinitePL ∧ ∀ p : square,
        (e p : E × ℝ) = (lineMap l r (p : ℝ × ℝ).1,
          α + (β - α) * (p : ℝ × ℝ).2) := by
  obtain ⟨K, hK, hspace⟩ := exists_finite_triangulation_square
  have hPL : FinitePiecewiseAffineOn (segmentProductCoordinates l r α β) square :=
    ⟨K, hK, hspace, K.affineOnFaces_affine _⟩
  have hex := hPL.exists_homeomorph_image (segmentProductCoordinates_injective hlr hαβ.ne).injOn
  rw [segmentProductCoordinates_image hαβ.le] at hex
  obtain ⟨e, he, heval⟩ := hex
  exact ⟨e, he, fun p => (heval p).trans (segmentProductCoordinates_apply l r α β p)⟩

end PLStrip
