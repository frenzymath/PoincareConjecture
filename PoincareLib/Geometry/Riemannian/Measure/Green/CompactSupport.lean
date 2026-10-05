import PoincareLib.Geometry.Riemannian.Measure.Green.Chart
import PoincareLib.Geometry.Riemannian.Measure.Green.Partition
import PoincareLib.Geometry.Riemannian.Measure.Exhaustion

/-!
# Compact-support Green identity

A finite smooth chart decomposition globalizes coordinate integration by parts
for the retained metric volume and Hessian-trace Laplacian. Neither completeness
nor compactness of the manifold is required. Connectedness supplies the compact
exhaustion used to construct a smooth partition of unity.

This is an integration prerequisite for Chow et al., *The Ricci Flow*, Part III,
Proposition 26.49, printed pp. 378--381.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The Laplacian paired with a compactly supported smooth test is integrable. -/
theorem integrable_mul_laplacian
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) :
    Integrable (fun x => u x * D.laplacian v x) g.volumeMeasure := by
  exact (hu.continuous.mul (D.continuous_laplacian hv)).integrable_of_hasCompactSupport
    hc.mul_right

/-- The gradient pairing with a compactly supported smooth test is integrable. -/
theorem integrable_inner_gradient
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) :
    Integrable (fun x => g.inner x (D.gradient u x) (D.gradient v x)) g.volumeMeasure := by
  exact (D.continuous_inner_gradient hu hv).integrable_of_hasCompactSupport
    (D.hasCompactSupport_inner_gradient hc v)

/-- The compact-support Green formula on a sigma-compact manifold. -/
theorem integral_mul_laplacian_of_sigmaCompact [SigmaCompactSpace M]
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) := by
  classical
  obtain ⟨s, w, hw, hwc, hws, hsum⟩ := exists_finite_chart_decomposition hu hc
  have hlocal (i : M) :
      (∫ x, w i x * D.laplacian v x ∂g.volumeMeasure) =
        -(∫ x, g.inner x (D.gradient (w i) x) (D.gradient v x) ∂g.volumeMeasure) :=
    D.integral_mul_laplacian_of_tsupport_subset_chart
      (chartAt (EuclideanSpace ℝ (Fin n)) i).symm
      contMDiffOn_chart_symm contMDiffOn_chart (hw i) hv (hwc i) (hws i)
  have hgrad (x : M) : D.gradient u x = ∑ i ∈ s, D.gradient (w i) x := by
    rw [← funext hsum]
    exact D.gradient_finset_sum s w x (fun i _ => (hw i x).mdifferentiableAt (by simp))
  calc
    _ = ∫ x, ∑ i ∈ s, w i x * D.laplacian v x ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_mul, hsum]
    _ = ∑ i ∈ s, ∫ x, w i x * D.laplacian v x ∂g.volumeMeasure :=
      integral_finsetSum s (fun i _ => D.integrable_mul_laplacian (hw i) hv (hwc i))
    _ = -(∑ i ∈ s, ∫ x, g.inner x (D.gradient (w i) x) (D.gradient v x)
        ∂g.volumeMeasure) := by simp only [hlocal, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i ∈ s, g.inner x (D.gradient (w i) x) (D.gradient v x)
        ∂g.volumeMeasure) := by
      rw [integral_finsetSum s (fun i _ => D.integrable_inner_gradient (hw i) hv (hwc i))]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [hgrad, map_sum, sum_apply]

/-- Green's identity for a connected manifold, the retained scalar Laplacian,
and the retained intrinsic volume. It includes dimension zero. -/
theorem integral_mul_laplacian [PreconnectedSpace M]
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) := by
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  exact D.integral_mul_laplacian_of_sigmaCompact hu hv hc

/- The compact-support Green form is symmetric in its two smooth arguments.

This is the bilinear identity consumed by Dirichlet exhaustion and by the
finite-domain heat semigroup construction.  It is obtained by applying the
compact-support Green formula in both orders and using symmetry of the
Riemannian inner product. -/
theorem integral_mul_laplacian_comm [PreconnectedSpace M]
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hcu : HasCompactSupport u) (hcv : HasCompactSupport v) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      ∫ x, v x * D.laplacian u x ∂g.volumeMeasure := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [D.integral_mul_laplacian hu hv hcu,
    D.integral_mul_laplacian hv hu hcv]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change inner ℝ (D.gradient u x) (D.gradient v x) =
      inner ℝ (D.gradient v x) (D.gradient u x)
    rw [real_inner_comm])

/-- Formal symmetry only needs compact support of the test function. This
allows the other argument to be a positive-time heat-kernel slice. -/
theorem integral_mul_laplacian_comm_of_hasCompactSupport_left [PreconnectedSpace M]
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hcu : HasCompactSupport u) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      ∫ x, v x * D.laplacian u x ∂g.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hcu.isCompact
  obtain ⟨χ, hχzero, hχone, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (n := ⊤) (𝓡 n) isOpen_interior.isClosed_compl
    (K.isCompact (N + 1)).isClosed
    (disjoint_compl_left_iff.mpr (K.subset_interior_succ (N + 1)))
  have hχc : HasCompactSupport (χ : M → ℝ) := by
    apply HasCompactSupport.of_support_subset_isCompact (K.isCompact (N + 1 + 1))
    intro x hx
    by_contra hxK
    exact hx (hχzero (fun hxI => hxK (interior_subset hxI)))
  have hχgerm (x : M) (hx : x ∈ tsupport u) :
      (fun y => χ y * v y) =ᶠ[𝓝 x] v := by
    filter_upwards [isOpen_interior.mem_nhds (K.subset_interior_succ N (hN hx))] with y hy
    rw [hχone (interior_subset hy), Pi.one_apply, one_mul]
  have hgrad (x : M) (hx : x ∈ tsupport u) :
      D.gradient (fun y => χ y * v y) x = D.gradient v x := by
    unfold gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq (hχgerm x hx)]
  rw [D.integral_mul_laplacian hu hv hcu]
  calc
    _ = -(∫ x, g.inner x (D.gradient (fun y => χ y * v y) x) (D.gradient u x)
        ∂g.volumeMeasure) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport u
      · rw [hgrad x hx]
        change inner ℝ (D.gradient u x) (D.gradient v x) =
          inner ℝ (D.gradient v x) (D.gradient u x)
        exact real_inner_comm _ _
      · simp [D.gradient_eq_zero_of_notMem_tsupport hx]
    _ = ∫ x, (χ x * v x) * D.laplacian u x ∂g.volumeMeasure :=
      (D.integral_mul_laplacian (χ.contMDiff.mul hv) hu hχc.mul_right).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport u
      · have hxK : x ∈ K (N + 1) := K.subset_succ N (hN hx)
        rw [hχone hxK]
        simp
      · simp [D.laplacian_eq_zero_of_notMem_tsupport hx]

/-- A smooth compactly supported Laplacian can be paired with a continuous
function, without any global growth bound on that function. -/
theorem integrable_mul_laplacian_of_hasCompactSupport_right
    (D : LeviCivitaData g) {u v : M → ℝ} (hu : Continuous u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v) (hcv : HasCompactSupport v) :
    Integrable (fun x => u x * D.laplacian v x) g.volumeMeasure := by
  exact (hu.mul (D.continuous_laplacian hv)).integrable_of_hasCompactSupport
    (D.hasCompactSupport_laplacian hcv).mul_left

end PoincareMT.LeviCivitaData
