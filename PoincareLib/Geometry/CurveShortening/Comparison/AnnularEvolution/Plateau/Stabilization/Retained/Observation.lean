import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Projected.WeightedEnergy

/-!
# A genuine observation retaining the old factor linearly

Augment a closed chart observation of the circle product by the prescribed
observation of its base. The original product observation still supplies
injectivity and chart readers, while a fixed linear projection reads the
retained base observation exactly. This prepares weak projection without
assuming a nonlinear Sobolev chain or boundary-trace theorem.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- Augment a compact chart observation with a prescribed linearly readable base
observation. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_exists_retained_observation
    (P : M62.CircleProductData F circumference)
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) ∞ e) :
    ∃ (k : ℕ) (o : P.charts.Point → EuclideanSpace ℝ (Fin k))
      (L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)),
      ContMDiff (𝓡 (n + 1)) (𝓡 k) ∞ o ∧ IsClosedEmbedding o ∧
        M60.SUChartReadable (n := n + 1) o ∧
        ∀ q : P.charts.Point, L (o q) = e q.1 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let := P.charts.chartedSpace
  obtain ⟨d, w, hw, hwi, hread⟩ :=
    M60.suCompactObservation_exists (n := n + 1) (M := P.charts.Point)
  let A : EuclideanSpace ℝ (Fin (m + d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) :=
    EuclideanSpace.finAddEquivProd
  let o : P.charts.Point → EuclideanSpace ℝ (Fin (m + d)) :=
    fun q => A.symm (e q.1, w q)
  let L : EuclideanSpace ℝ (Fin (m + d)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (ContinuousLinearMap.fst ℝ _ _).comp A.toContinuousLinearMap
  let R : EuclideanSpace ℝ (Fin (m + d)) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (ContinuousLinearMap.snd ℝ _ _).comp A.toContinuousLinearMap
  have hL (q : P.charts.Point) : L (o q) = e q.1 := by
    change (A (A.symm (e q.1, w q))).1 = e q.1
    rw [A.apply_symm_apply]
  have hR (q : P.charts.Point) : R (o q) = w q := by
    change (A (A.symm (e q.1, w q))).2 = w q
    rw [A.apply_symm_apply]
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞
      (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have ho : ContMDiff (𝓡 (n + 1)) (𝓡 (m + d)) ∞ o :=
    A.symm.toDiffeomorph.contMDiff.comp ((he.comp hfst).prodMk_space hw)
  have hoi : Function.Injective o := by
    intro q q' h
    apply hwi.injective
    simpa only [hR] using congrArg R h
  refine ⟨m + d, o, L, ho, ho.continuous.isClosedEmbedding hoi, ?_, hL⟩
  intro q
  obtain ⟨b, hb, S, hS⟩ := hread q
  refine ⟨b, hb, S.comp R, ?_⟩
  simpa only [ContinuousLinearMap.comp_apply, hR] using hS

end PoincareMT.M64
