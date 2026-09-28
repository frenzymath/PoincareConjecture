import PoincareConjecture.Proofs.M14.Sec6_2_FirstVariation

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem horizontalRicci_smul_right (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : G.Point) (v w : G.Horizontal q) (c : ℝ) :
    horizontalRicci G.leafwise q v (c • w) = c * horizontalRicci G.leafwise q v w := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  obtain ⟨A, hA⟩ := H.ricci_tensor.1 q
  have heval (v w : G.Horizontal q) : horizontalRicci G.leafwise q v w = A ![v, w] := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using hA ![v, w]
  rw [H.ricci_symmetric q v, heval, H.ricci_symmetric q v w, heval]
  simpa only [smul_eq_mul, Matrix.vecCons] using A.cons_smul ![v] c w

theorem squareRootEulerResidual_smul (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) (s c : ℝ) (W : G.Horizontal (R.curve s)) :
    M14SquareRootEulerResidual G R E s (c • W) = c * M14SquareRootEulerResidual G R E s W := by
  simp only [M14SquareRootEulerResidual, map_smul, Submodule.coe_smul,
    horizontalRicci_smul_right hM12, smul_eq_mul]
  ring

theorem squareRootEulerResidual_extension_independent
    (E₁ E₂ : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (W : G.Horizontal (R.curve s)) :
    M14SquareRootEulerResidual G R E₁ s W = M14SquareRootEulerResidual G R E₂ s W := by
  have hd := horizontalCovariantDerivative_extension_independent E₁ E₂ hs
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs)
    ((R.smooth.mono R.interval_subset s hs).mdifferentiableWithinAt (by simp))
  simp only [M14SquareRootEulerResidual, hd]

noncomputable def variationEulerDensity (V : M14LVariationData G p R) (s : ℝ) : ℝ :=
  derivWithin (variationBoundaryPair V) (M14SqrtParameterInterval τ₁ τ₂) s -
    M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
      (variationActionDensity V) (s, 0)

theorem variationEulerDensity_contDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) :
    ContDiffOn ℝ ∞ (variationEulerDensity V) (M14SqrtParameterInterval τ₁ τ₂) := by
  have hC : UniqueDiffOn ℝ (M14SqrtParameterInterval τ₁ τ₂) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hraw := (M08.variationParameterDeriv_contDiffOn hC hP (variationActionDensity V)
    (variationActionDensity_contDiffOn hM12 V)).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ hs => ⟨hs, hzero⟩)
  exact ((variationBoundaryPair_contDiffOn V).derivWithin hC (m := ∞) (by simp)).sub hraw

theorem variationEulerDensity_eq_residual (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (V : M14LVariationData G p R)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    variationEulerDensity V s = M14SquareRootEulerResidual G R E s (M14VariationField V s) := by
  obtain ⟨D⟩ := exists_variationDerivativeData V
  have hid := firstVariation_density_identity hCoordinates hM12 V D hs
  rw [squareRootEulerResidual_extension_independent D.base_extension E
    (Ioo_subset_Icc_self hs)] at hid
  unfold variationEulerDensity
  linarith

end PoincareConjecture.M14
