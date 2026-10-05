import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CanonicalCoreFlow

/-!
# Global coefficient identity for the canonical core flow

The canonical whole-space chart has identity differential everywhere.
Its actual flow coefficients therefore equal the original coefficients
under the ambient identity map, as whole functions and at all total
times. This is Morgan-Tian Section 12.5, pp. 309-319 and
core-energy-comparison-api.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy

/-- The actual core chart and ambient identity have equal coefficient
fields everywhere, so all ordinary spatial jets agree
(Section 12.5, pp. 309-319). -/
theorem canonicalCoreFlow_chart_coefficients {n : ℕ} {J : Set ℝ}
    (F : RicciFlow n (V n) J) :
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (p : (univ : Set (V n))),
      ((canonicalCoreFlow F).metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm =
        (F.metric t).pullbackCoefficients id := by
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V n))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 n) (n := ∞)
  intro t p
  funext x
  let xU : (univ : Set (V n)) := ⟨x, mem_univ _⟩
  calc
    _ = ((canonicalCoreFlow F).metric t).inner xU :=
      RiemannianMetric.pullbackCoefficients_canonicalChart univ isOpen_univ
        ((canonicalCoreFlow F).metric t) p xU
    _ = (F.metric t).inner x := canonicalCoreFlow_inner F t xU
    _ = (F.metric t).pullbackCoefficients id x := by
      ext u v
      change (F.metric t).inner x u v = (F.metric t).inner (id x)
        (mfderiv (𝓡 n) (𝓡 n) id x u) (mfderiv (𝓡 n) (𝓡 n) id x v)
      rw [mfderiv_id]
      rfl

end PoincareMT.M34
