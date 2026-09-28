import PoincareConjecture.Proofs.M14.Sec6_5_RegularSpatialDerivative

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

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

theorem initialVectorVariation_field_at (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s r : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos))
    (hV : ∀ t ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
      V.squareFamily t u = E.gamma (Z + u • W) t)
    (hr : r ∈ M14SqrtParameterInterval 0 (s ^ 2)) (hrsurv : (Z, r) ∈ E.domain) :
    HEq (M14VariationField V r) (E.differential Z r hrsurv W) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hval : (M14VariationField V r).val =
      mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => V.squareFamily r u) 0 (1 : ℝ) := by
    exact (horizontal_transport_val (V.square_base r) (M14EndpointVariationField V r 0)).trans
      (endpointVariationField_val_eq_tangent V hr hzero)
  have hline : HasDerivAt (fun u : ℝ => Z + u • W) W 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
  have hlineM : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, G.Horizontal x))
      (fun u : ℝ => Z + u • W) 0 (1 : ℝ) = W := by
    rw [mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    change (1 : ℝ) • W = W
    exact one_smul ℝ W
  have hchain := mfderiv_comp_apply_of_eq (x := (0 : ℝ))
    ((exponentialFamily_gamma_slice_contMDiffAt E hrsurv).mdifferentiableAt (by simp))
    hline.differentiableAt.mdifferentiableAt (by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [hlineM] at hchain
  have heq : (fun u => V.squareFamily r u) = (fun u => E.gamma (Z + u • W) r) :=
    funext (hV r hr)
  rw [heq] at hval
  apply horizontal_heq_of_val_eq (exponential_square_curve_eq E Z hs hpos hr)
  exact hval.trans (hchain.trans (E.differential_pointwise_mfderiv Z r hrsurv W).symm)

theorem initialVectorVariation_initialFixed (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos))
    (hV : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
      V.squareFamily r u = E.gamma (Z + u • W) r) : V.left_endpoint_fixed := by
  apply V.left_endpoint_fixed_spec.mpr
  intro u hu
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 (s ^ 2) :=
    ⟨by simp, Real.sqrt_nonneg _⟩
  have h := V.square_agrees 0 hzero u hu
  simpa only [zero_pow (by decide : 2 ≠ 0), hV 0 hzero u, E.gamma_at_zero,
    (E.path Z s hs hpos).curve_start] using h.symm

theorem initialVectorVariation_action_germ (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hz : (Z, s) ∈ M14JointDomain G E)
    (V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos))
    (hmem : ∀ u ∈ V.parameterDomain, (Z + u • W, s) ∈ E.domain)
    (hV : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
      V.squareFamily r u = E.gamma (Z + u • W) r) :
    M14VariationAction V =ᶠ[𝓝 0]
      (fun u => (2 * s) * M14ReducedLengthAt G T 0 x (V.squareFamily s u)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hline : ContinuousAt (fun u : ℝ => Z + u • W) 0 := by fun_prop
  have hU : H.carrier ∈ 𝓝 (Z + (0 : ℝ) • W) := by
    simpa only [zero_smul, add_zero] using H.carrier_open.mem_nhds hZH
  have hP : V.parameterDomain ∈ 𝓝 (0 : ℝ) := by
    rw [V.parameterDomain_eq]
    exact isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)
  filter_upwards [hline.preimage_mem_nhds hU, hP] with u hu huP
  have hbranch := stableInitialVector_unique_branch E ((H.carrier_exact _).mp hu)
  rw [initialVectorVariation_action E Z W hs hpos V hmem hV huP, hV s hsC u,
    reducedLengthAt_eq_normalized_action E (hmem u huP) hpos
      (exponentialPath_minimizing_of_uniqueBranch E hpos (hmem u huP) hbranch)]
  exact (mul_div_cancel₀ _ (mul_pos zero_lt_two hpos).ne').symm

end PoincareConjecture.M14
