import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSlices
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector
import PoincareConjecture.Proofs.M14.Sec6_4_FixedEndpointBoundary
import PoincareConjecture.Proofs.M14.Sec6_2_VariationClock










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : (h.symm ▸ v : G.Horizontal r).val = v.val := by
  cases h
  rfl

private theorem horizontal_heq_of_val_eq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : v.val = w.val) : HEq v w := by
  cases h
  exact heq_of_eq (Subtype.ext hv)




theorem initialVectorVariation_field_zero (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos))
    (hV : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
      V.squareFamily r u = E.gamma (Z + u • W) r) :
    M14VariationField V 0 = 0 := by
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 (s ^ 2) :=
    ⟨by simp, Real.sqrt_nonneg _⟩
  apply variationField_eq_zero_of_constant V
  intro u _
  rw [hV 0 hzero u, hV 0 hzero 0, E.gamma_at_zero, E.gamma_at_zero]




theorem initialVectorVariation_field_terminal (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos))
    (hV : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
      V.squareFamily r u = E.gamma (Z + u • W) r) :
    HEq (M14VariationField V s) (E.differential Z s hs W) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le, mem_Icc]
    exact ⟨hpos.le, le_rfl⟩
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hval : (M14VariationField V s).val =
      mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => V.squareFamily s u) 0 (1 : ℝ) := by
    exact (horizontal_transport_val (V.square_base s) (M14EndpointVariationField V s 0)).trans
      (endpointVariationField_val_eq_tangent V hsC hzero)
  have hline : HasDerivAt (fun u : ℝ => Z + u • W) W 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
  have hlineM : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, G.Horizontal x))
      (fun u : ℝ => Z + u • W) 0 (1 : ℝ) = W := by
    rw [mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    change (1 : ℝ) • W = W
    exact one_smul ℝ W
  have hchain := mfderiv_comp_apply_of_eq (x := (0 : ℝ))
    ((exponentialFamily_gamma_slice_contMDiffAt E hs).mdifferentiableAt (by simp))
    hline.differentiableAt.mdifferentiableAt (by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [hlineM] at hchain
  have heq : (fun u => V.squareFamily s u) = (fun u => E.gamma (Z + u • W) s) :=
    funext (hV s hsC)
  rw [heq] at hval
  apply horizontal_heq_of_val_eq (exponential_square_curve_eq E Z hs hpos hsC)
  exact hval.trans (hchain.trans (E.differential_pointwise_mfderiv Z s hs W).symm)

end PoincareConjecture.M14
