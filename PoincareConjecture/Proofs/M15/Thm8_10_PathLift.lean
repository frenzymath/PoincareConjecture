import PoincareConjecture.Proofs.M15.Thm8_10_OrdinaryProduct
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.RealTime
import PoincareConjecture.Definitions.Ch06.LGeometry










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}



theorem ordinaryProduct_backwardPath_lift
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    {T a b : ℝ} (q : BackwardTimePath F T a b) :
    ∃ p : M14BackwardPath (ordinaryProductTransport F P) T a b
      (P.product.productCylinder.toSpacetime
        ((⟨T - a, q.time_mem a ⟨le_rfl, q.ordered.le⟩⟩, q.curve a)))
      (P.product.productCylinder.toSpacetime
        ((⟨T - b, q.time_mem b ⟨q.ordered.le, le_rfl⟩⟩, q.curve b))),
      ∀ (s : ℝ) (hs : s ∈ Icc a b),
        P.product.productCylinder.toSpacetime
          ((⟨T - s, q.time_mem s hs⟩, q.curve s)) = p.curve s := by
  let G := ordinaryProductTransport F P
  let D := P.product.timeIntervals.interval I
  let e := P.product.productCylinder
  let g := ordinaryProductCylinderMetric F P
  let α : ℝ → D.Point := fun s => D.realParam (T - s)
  let L : ℝ → D.Point × M := fun s => (α s, q.curve s)
  let γ : ℝ → G.Point := e.toSpacetime ∘ L
  let v : ∀ s, G.Horizontal (γ s) := fun s =>
    g.spatialTangentEquiv (α s) (q.curve s) (curveVelocity (n := n) q.curve s)
  have hαval (s : ℝ) (hs : s ∈ Icc a b) : (α s).val = T - s :=
    D.realParam_val (q.time_mem s hs)
  have hα : ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) 1 α (Icc a b) :=
    (D.realParam_smoothOn.of_le (by simp)).comp
      (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn q.time_mem
  have hL : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) 1 L (Ioo a b) :=
    (hα.mono Ioo_subset_Icc_self).prodMk q.regular
  have hγ : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) 1 γ (Ioo a b) :=
    (e.smooth.of_le (by simp)).comp_contMDiffOn hL
  have hlift (s : ℝ) (hs : s ∈ Icc a b) :
      e.toSpacetime ((⟨T - s, q.time_mem s hs⟩, q.curve s)) = γ s := by
    have ht : α s = ⟨T - s, q.time_mem s hs⟩ := Subtype.ext (hαval s hs)
    change e.toSpacetime _ = e.toSpacetime (α s, q.curve s)
    rw [ht]
  have hclock (s : ℝ) (hs : s ∈ Icc a b) : G.spacetime.timeFunction (γ s) = T - s :=
    (e.time_eq (L s)).trans (hαval s hs)
  have hderiv (s : ℝ) (hs : s ∈ Ioo a b) :
      mfderiv 𝓘(ℝ) (spacetimeModel n) γ s 1 =
        -G.spacetime.timeVector (γ s) + (v s).val := by
    have hnh : Ioo a b ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
    have hu : UniqueDiffWithinAt ℝ (Ioo a b) s := isOpen_Ioo.uniqueDiffWithinAt hs
    have ht := q.time_mem s (Ioo_subset_Icc_self hs)
    have hsub : HasDerivAt (fun r : ℝ => T - r) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub T
    have hsubm : MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ)
        (fun r : ℝ => T - r) (Ioo a b) s :=
      hsub.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
    have hsubD : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (fun r : ℝ => T - r)
        (Ioo a b) s 1 = -1 := by
      rw [mfderivWithin_eq_fderivWithin]
      simpa using! congrArg (fun A : ℝ →L[ℝ] ℝ => A 1)
        (hsub.hasFDerivAt.hasFDerivWithinAt.fderivWithin hu)
    have hαd : mfderiv 𝓘(ℝ) (𝓡∂ 1) α s 1 = -D.positiveTangent (α s) := by
      rw [← mfderivWithin_of_mem_nhds hnh]
      change mfderivWithin 𝓘(ℝ) (𝓡∂ 1) (D.realParam ∘ (fun r => T - r))
        (Ioo a b) s 1 = _
      rw [mfderivWithin_comp s
        ((D.realParam_smoothOn (T - s) ht).mdifferentiableWithinAt (by simp))
        hsubm (fun r hr => q.time_mem r (Ioo_subset_Icc_self hr)) hu.uniqueMDiffWithinAt]
      change mfderivWithin 𝓘(ℝ) (𝓡∂ 1) D.realParam I.domain (T - s)
        (mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (fun r : ℝ => T - r) (Ioo a b) s 1) = _
      rw [hsubD, D.realParam_mfderivWithin ht]
      change (D.inclusionDerivative (α s)).symm (-1) =
        -(D.inclusionDerivative (α s)).symm 1
      exact map_neg _ _
    have hαm := ((hα.mono Ioo_subset_Icc_self s hs).mdifferentiableWithinAt
      (by simp)).mdifferentiableAt hnh
    have hqm := ((q.regular s hs).mdifferentiableWithinAt (by simp)).mdifferentiableAt hnh
    have hLm := ((hL s hs).mdifferentiableWithinAt (by simp)).mdifferentiableAt hnh
    have hLd : mfderiv 𝓘(ℝ) (spacetimeModel n) L s 1 =
        (-D.positiveTangent (α s), curveVelocity (n := n) q.curve s) := by
      change mfderiv 𝓘(ℝ) ((𝓡∂ 1).prod (𝓡 n))
        (fun r => (α r, q.curve r)) s 1 = _
      rw [mfderiv_prodMk hαm hqm]
      change (mfderiv 𝓘(ℝ) (𝓡∂ 1) α s 1,
        mfderiv 𝓘(ℝ) (𝓡 n) q.curve s 1) = _
      rw [hαd]
      rfl
    change mfderiv 𝓘(ℝ) (spacetimeModel n) (e.toSpacetime ∘ L) s 1 = _
    rw [mfderiv_comp_apply s (e.smooth.mdifferentiableAt (by simp)) hLm, hLd]
    rw [mfderiv_prod_eq_add_apply (e.smooth.mdifferentiableAt (by simp)),
      map_neg, e.worldline_derivative, ← g.spatialTangentEquiv_eq]
    rfl
  have hdensity (s : ℝ) (hs : s ∈ Ioo a b) :
      M14RawLIntegrand G γ v s = backwardLIntegrand F T q.curve s := by
    have hc := ordinaryProduct_moving_calculus hM12 F P
    unfold M14RawLIntegrand backwardLIntegrand
    change Real.sqrt s * (horizontalScalarCurvature G.leafwise
      (e.toSpacetime (α s, q.curve s)) +
      G.spacetime.horizontalMetric.inner (e.toSpacetime (α s, q.curve s))
        (g.spatialTangentEquiv (α s) (q.curve s) (curveVelocity (n := n) q.curve s))
        (g.spatialTangentEquiv (α s) (q.curve s) (curveVelocity (n := n) q.curve s))) = _
    erw [← hc.scalar_eq, ← g.metric_eq]
    change Real.sqrt s * ((F.connection (α s).val).scalarCurvature (q.curve s) +
      (F.metric (α s).val).inner (q.curve s) _ _) = _
    rw [hαval s (Ioo_subset_Icc_self hs)]
  refine ⟨{
    tau_nonneg := q.nonnegative
    tau_lt := q.ordered
    base_time := e.time_eq _
    endpoint_time := e.time_eq _
    curve := γ
    curve_start := (hlift a ⟨le_rfl, q.ordered.le⟩).symm
    curve_end := (hlift b ⟨q.ordered.le, le_rfl⟩).symm
    curve_time := hclock
    curve_continuous := e.smooth.continuous.comp_continuousOn
      (hα.continuousOn.prodMk q.continuous)
    curve_regular := hγ
    horizontal_velocity := v
    derivative_eq := hderiv
    action_integrable := ?_
  }, hlift⟩
  apply q.l_integrable.congr_uIoo
  intro s hs
  exact (hdensity s (by simpa only [uIoo_of_le q.ordered.le] using hs)).symm

end PoincareConjecture.Proofs.M15
