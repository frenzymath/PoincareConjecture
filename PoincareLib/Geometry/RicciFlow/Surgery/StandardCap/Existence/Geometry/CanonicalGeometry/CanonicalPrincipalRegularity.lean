import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CanonicalFlowRegularity

/-!+# Regularity of actual canonical principal coefficients

The native metric is positive at every point. Smooth inversion therefore
preserves its actual joint regularity on the included time-space domain.
No uniform ellipticity outside the cutoff support is needed. This is
Morgan-Tian Section 12.5, pp. 309-319 and canonical-local-integral-energy.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy Proofs.M03

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

/-- The actual inverse metric is jointly smooth in fixed canonical
coordinates on the included domain (Section 12.5, pp. 309-319). -/
theorem canonicalDomain_contDiffOn_flow_inverse
    {dH : ℕ} (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n U J) (p : U),
      ContDiffOn (F := (V n →L[ℝ] ℝ) →L[ℝ] V n) ℝ ∞
        (fun z : ℝ × V n =>
          ((F.metric z.1).inner ((extChartAt (𝓡 n) p).symm z.2) : FH n).inverse) (J ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F p
  have hg := canonicalDomain_contDiffOn_flow_metric U hU qH F p
  intro z hz
  have hi : ((F.metric z.1).inner ((extChartAt (𝓡 n) p).symm z.2) : FH n).IsInvertible :=
    isInvertible_bilinear_of_pos (E := V n) ((F.metric z.1).pos _)
  have hinv : ContDiffAt ℝ ∞ (fun B : FH n => B.inverse)
      ((F.metric z.1).inner ((extChartAt (𝓡 n) p).symm z.2) : FH n) :=
    hi.contDiffAt_map_inverse
  exact hinv.comp_contDiffWithinAt z (hg z hz)

/-- Every actual principal matrix entry is jointly smooth, including
included time boundaries (Section 12.5, pp. 309-319). -/
theorem canonicalDomain_contDiffOn_principal_entry
    {dH : ℕ} (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n U J) (p : U) (i j : Fin n),
      ContDiffOn ℝ ∞ (fun z : ℝ × V n => EuclideanSpace.proj i
        (((F.metric z.1).inner ((extChartAt (𝓡 n) p).symm z.2) : FH n).inverse
          (EuclideanSpace.proj j))) (J ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F p i j
  exact (EuclideanSpace.proj i : V n →L[ℝ] ℝ).contDiff.comp_contDiffOn
    ((canonicalDomain_contDiffOn_flow_inverse U hU qH F p).clm_apply
      (contDiffOn_const (c := (EuclideanSpace.proj j : V n →L[ℝ] ℝ))))

end PoincareMT.M34
