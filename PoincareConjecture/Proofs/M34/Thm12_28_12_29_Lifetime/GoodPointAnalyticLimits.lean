import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.GoodPointAnalytic
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryScalarGradientLimits
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryScalarEvolutionLimits

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11_eventually_scalar_bounds
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) {A : ℝ}
    (hgradient :
      letI := C.limit.carrier.topologicalSpace
      letI := C.limit.carrier.chartedSpace
      letI := C.limit.carrier.isManifold
      scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) C.limit.base < A)
    (hevolution :
      letI := C.limit.carrier.topologicalSpace
      letI := C.limit.carrier.chartedSpace
      letI := C.limit.carrier.isManifold
      |(C.limit.flow.connection 0).laplacian (C.limit.flow.connection 0).scalarCurvature
        C.limit.base + 2 * (C.limit.flow.connection 0).ricciNormSq C.limit.base| < A) :
    ∀ᶠ k : ℕ in atTop,
      scalarGradientNorm ((G).metric (p (C.subsequence k)).1)
        ((G).connection (p (C.subsequence k)).1) (p (C.subsequence k)).2 ≤
          A * ((G).scalar (p (C.subsequence k))) ^ (3 / 2 : ℝ) ∧
      |((G).connection (p (C.subsequence k)).1).laplacian
          ((G).connection (p (C.subsequence k)).1).scalarCurvature (p (C.subsequence k)).2 +
        2 * ((G).connection (p (C.subsequence k)).1).ricciNormSq (p (C.subsequence k)).2| ≤
          A * ((G).scalar (p (C.subsequence k))) ^ 2 := by
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  let gradient : (G).point → ℝ := fun z =>
    scalarGradientNorm ((G).metric z.1) ((G).connection z.1) z.2
  let evolution : (G).point → ℝ := fun z =>
    ((G).connection z.1).laplacian ((G).connection z.1).scalarCurvature z.2 +
      2 * ((G).connection z.1).ricciNormSq z.2
  have hg := ordinaryChapter11_tendsto_scalarGradient_zero R p hpositive hdiverges C
    hJ C.limit.base
  have he := ordinaryChapter11_tendsto_scalarEvolution_zero R p hpositive hdiverges C
    hJ C.limit.base
  filter_upwards [hg.eventually (eventually_lt_nhds hgradient),
    he.abs.eventually (eventually_lt_nhds hevolution)] with k hgk hek
  change gradient ((C.embedding k).pointMap 0 (h0 k) C.limit.base) /
    ((G).scalar (p (C.subsequence k))) ^ (3 / 2 : ℝ) < A at hgk
  change |evolution ((C.embedding k).pointMap 0 (h0 k) C.limit.base) /
    ((G).scalar (p (C.subsequence k))) ^ 2| < A at hek
  rw [C.base_preserving k (h0 k)] at hgk hek
  have hq : 0 < ((G).scalar (p (C.subsequence k))) ^ 2 :=
    sq_pos_of_pos (hpositive (C.subsequence k))
  rw [abs_div, abs_of_pos hq] at hek
  exact ⟨((div_lt_iff₀ (Real.rpow_pos_of_pos (hpositive (C.subsequence k)) _)).mp hgk).le,
    ((div_lt_iff₀ hq).mp hek).le⟩

theorem ordinaryChapter11_eventually_goodPoint
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) {epsilon c A : ℝ}
    (hgradient :
      letI := C.limit.carrier.topologicalSpace
      letI := C.limit.carrier.chartedSpace
      letI := C.limit.carrier.isManifold
      scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) C.limit.base < A)
    (hevolution :
      letI := C.limit.carrier.topologicalSpace
      letI := C.limit.carrier.chartedSpace
      letI := C.limit.carrier.isManifold
      |(C.limit.flow.connection 0).laplacian (C.limit.flow.connection 0).scalarCurvature
        C.limit.base + 2 * (C.limit.flow.connection 0).ricciNormSq C.limit.base| < A)
    (hcanonical : ∀ᶠ k : ℕ in atTop, Nonempty (GeneralizedCanonicalControl (F := G)
      (p (C.subsequence k)).1 (p (C.subsequence k)).2 epsilon c)) :
    ∀ᶠ k : ℕ in atTop, Chapter11GoodPoint (G) epsilon c A (p (C.subsequence k)) := by
  filter_upwards [ordinaryChapter11_eventually_scalar_bounds R p hpositive hdiverges C
    hJ hgradient hevolution, hcanonical] with k hk hc
  exact chapter11GoodPoint_of_scalar_bounds (p (C.subsequence k)) hc hk.1 hk.2

end PoincareConjecture.M34
