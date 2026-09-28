import PoincareConjecture.Proofs.M34.Standard.CanonicalCoreFlow











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

open DifferenceEnergy




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

end PoincareConjecture.M34
