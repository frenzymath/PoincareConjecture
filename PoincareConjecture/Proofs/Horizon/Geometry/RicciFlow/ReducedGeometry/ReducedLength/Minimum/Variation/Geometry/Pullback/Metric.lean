import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPairBase








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in
theorem parametricExtension_fixedMetric_pair_contMDiffAt
    (g : RiemannianMetric n M) {C : Set ℝ} {α : ℝ → M}
    {Y : ∀ r, TangentSpace (𝓡 n) (α r)}
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} {y : M}
    (hE : (s, y) ∈ E.domain) (W : ∀ x : M, TangentSpace (𝓡 n) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (W x)) y) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × M ↦ g.inner z.2 (E.extension z.1 z.2) (W z.2)) (s, y) := by
  have hmetric : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))) ∞
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk'
        (E := fun p : M ↦ TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ)
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        z.2 (g.inner z.2)) (s, y) :=
    g.contMDiff.contMDiffAt.comp (s, y)
      (show ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) ∞
        (Prod.snd : ℝ × M → M) (s, y) from contMDiffAt_snd)
  have hfield := (E.smooth (s, y) hE).contMDiffAt (E.open_domain.mem_nhds hE)
  have htest := hW.comp (s, y)
    (show ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) ∞
      (Prod.snd : ℝ × M → M) (s, y) from contMDiffAt_snd)
  have h : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) z.2
        (g.inner z.2 (E.extension z.1 z.2) (W z.2))) (s, y) := by
    apply ContMDiffAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact hmetric
    · exact hfield
    · exact htest
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffAt_totalSpace.mp h).2

set_option maxHeartbeats 1000000 in
theorem pullbackCovariantDerivative_metric_derivative {J C : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ r, TangentSpace (𝓡 n) (α r)}
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (W : ∀ x : M, TangentSpace (𝓡 n) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (W x)) (α s)) :
    HasDerivAt (fun r ↦ (F.metric (time s)).inner (α r)
        (E.extension r (α r)) (W (α r)))
      ((F.metric (time s)).inner (α s)
          (pullbackCovariantDerivative F time α Y C E s) (W (α s)) +
        (F.metric (time s)).inner (α s) (Y s)
          ((F.connection (time s)).connection W (α s)
            (curveVelocityWithin (n := n) α C s))) s := by
  let g := F.metric (time s)
  let D := F.connection (time s)
  have hvel : curveVelocityWithin (n := n) α C s = curveVelocity (n := n) α s := by
    unfold curveVelocityWithin curveVelocity
    rw [mfderivWithin_eq_mfderiv hC.uniqueMDiffWithinAt hα]
  have hEs := (parametricExtension_contMDiffAt_space E (E.graph_mem s hs)).mdifferentiableAt
    (by simp)
  have hspace : mvfderiv (𝓡 n)
      (fun x ↦ g.inner x (E.extension s x) (W x)) (α s) (curveVelocity (n := n) α s) =
      g.inner (α s) (D.connection (E.extension s) (α s) (curveVelocity (n := n) α s))
        (W (α s)) + g.inner (α s) (E.extension s (α s))
          (D.connection W (α s) (curveVelocity (n := n) α s)) := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h := D.metricCompatible.mvfderiv_inner_eq
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (curveVelocity (n := n) α s))
      hEs (hW.mdifferentiableAt (by simp))
    change mvfderiv (𝓡 n) (fun x ↦ g.inner x (E.extension s x) (W x)) (α s)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (curveVelocity (n := n) α s) (α s)) =
      g.inner (α s) (D.connection (E.extension s) (α s)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (curveVelocity (n := n) α s) (α s)))
        (W (α s)) + g.inner (α s) (E.extension s (α s))
        (D.connection W (α s)
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (curveVelocity (n := n) α s) (α s))) at h
    simpa only [FiberBundle.extend_apply_self] using h
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (α s)) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have htime : HasDerivAt (fun r ↦ g.inner (α s) (E.extension r (α s)) (W (α s)))
      (g.inner (α s) (deriv (fun r ↦ E.extension r (α s)) s) (W (α s))) s :=
    ((g.inner (α s)).flip (W (α s))).hasFDerivAt.comp_hasDerivAt s
      (parametricExtension_differentiableAt_time E (E.graph_mem s hs)).hasDerivAt
  have h := scalar_graph_hasDerivAt _
    ((parametricExtension_fixedMetric_pair_contMDiffAt g E (E.graph_mem s hs) W hW).mdifferentiableAt
      (by simp)) hα
  rw [htime.deriv, hspace, ← hvel, E.agrees s hs] at h
  convert h using 1
  simp only [pullbackCovariantDerivative, map_add, ContinuousLinearMap.add_apply]
  ring

set_option maxHeartbeats 1000000 in
theorem pullbackCovariantDerivative_extension_independent {J C : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ r, TangentSpace (𝓡 n) (α r)}
    (E₁ E₂ : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C E₁ s =
      pullbackCovariantDerivative F time α Y C E₂ s := by
  let g := F.metric (time s)
  let v := pullbackCovariantDerivative F time α Y C E₁ s -
    pullbackCovariantDerivative F time α Y C E₂ s
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (W x)) (α s) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have h₁ := pullbackCovariantDerivative_metric_derivative F time E₁ hs hC hα W hW
  have h₂ := pullbackCovariantDerivative_metric_derivative F time E₂ hs hC hα W hW
  have h₁' := h₁.hasDerivWithinAt.congr_of_mem
    (show ∀ r ∈ C, g.inner (α r) (E₂.extension r (α r)) (W (α r)) =
        g.inner (α r) (E₁.extension r (α r)) (W (α r)) from by
      intro r hr
      rw [E₁.agrees r hr, E₂.agrees r hr]) hs
  have heq := (h₁'.derivWithin hC).symm.trans (h₂.hasDerivWithinAt.derivWithin hC)
  have hWself : W (α s) = v := FiberBundle.extend_apply_self _ _
  rw [hWself] at heq
  have hz : g.inner (α s) v v = 0 := by
    calc
      _ = g.inner (α s) (pullbackCovariantDerivative F time α Y C E₁ s) v -
          g.inner (α s) (pullbackCovariantDerivative F time α Y C E₂ s) v :=
        congrArg (fun L : TangentSpace (𝓡 n) (α s) →L[ℝ] ℝ ↦ L v)
          ((g.inner (α s)).map_sub _ _)
      _ = 0 := by dsimp only [g]; linarith
  by_contra hne
  exact (ne_of_gt (g.pos (α s) v (sub_ne_zero.mpr hne))) hz

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
