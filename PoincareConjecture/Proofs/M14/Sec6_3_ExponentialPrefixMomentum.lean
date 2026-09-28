import PoincareConjecture.Proofs.M14.Sec6_3_EndpointPrefixDifferential
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialLineRegularity
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixGaugeVelocity

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponential_prefixAction_fderiv_eventually
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x)
    {b c : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hsurv : ∀ r ∈ U, (Z + r • W, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j)
    (D : GaugeEndpointFamily (fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1)
      U T 0 b c 0 j lift)
    {V : Set G.Point} (hV : IsOpen V)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift V)
    (hright : ∀ q ∈ V, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hcenter : E.gamma Z c ∈ V) :
    let f := fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ d : ℝ × EuclideanSpace ℝ (Fin n),
      fderiv ℝ D.prefixAction (r, (lift (f (c, r))).2.val) d =
        ((G.gaugeCover.metric j).metric (lift (f (c, 0))).1.val).inner
          (lift (f (c, r))).2 (deriv (fun s => (lift (f (s, r))).2.val) c) d.2 := by
  let f := fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1
  have hzero : (0 : ℝ) ∈ U := D.parameter_subset _ D.center_mem
  have hFc : ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun r => f (c, r)) 0 := by
    have h := (exponentialLine_contMDiffAt E Z W hU hsurv hc hzero).comp 0
      (contMDiffAt_const.prodMk contMDiffAt_id)
    exact h
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), f (c, r) ∈ V :=
    hFc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by
      simpa only [f, zero_smul, add_zero] using hcenter))
  filter_upwards [D.diagonal_eventually_mem, hnear] with r hr hrV
  have hrU : r ∈ U := D.parameter_subset _ hr
  have hsurvC : (Z + r • W, c) ∈ E.domain :=
    (E.maximal_lifetime _).out (E.domain_zero _) (hsurv r hrU) ⟨hc.1.le, hc.2.le⟩
  let R := E.square_path (Z + r • W) c hsurvC hc.1
  have hC : M14SqrtParameterInterval 0 (c ^ 2) = Icc 0 c := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hc.1.le]
  have hbase : EqOn R.curve (fun s => f (s, r)) (M14SqrtParameterInterval 0 (c ^ 2)) :=
    fun _ hs => exponential_square_curve_eq E (Z + r • W) hsurvC hc.1 hs
  have hsc : c ∈ M14SqrtParameterInterval 0 (c ^ 2) := hC.symm ▸ ⟨hc.1.le, le_rfl⟩
  have hF := exponentialLine_contMDiffAt E Z W hU hsurv hc hrU
  have hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun s => f (s, r)) c := by
    have h := hF.comp c (contMDiffAt_id.prodMk contMDiffAt_const)
    exact h.mdifferentiableAt (by simp)
  have hrec : (fun s => f (s, r)) =ᶠ[𝓝 c]
      (fun s => (G.gaugeCover.cylinder j).toSpacetime (lift (f (s, r)))) := by
    filter_upwards [hα.continuousAt.preimage_mem_nhds (hV.mem_nhds hrV)] with s hs
    exact (hright _ hs).symm
  have hvel := squareRootVelocity_gauge_continuation R (fun s => f (s, r)) hbase hsc hα j lift
    (((hlift _ hrV).contMDiffAt (hV.mem_nhds hrV)).mdifferentiableAt (by simp)) hrec
  obtain ⟨hy, hmark⟩ := D.marked _ hr
  have hrecovery := D.recovery _ hr c ⟨hc.1.le, hc.2.le⟩
  have htime : (lift (f (c, r))).1 = (lift (f (c, 0))).1 := by
    have hpoint : (G.gaugeCover.cylinder j).toSpacetime (lift (f (c, r))) =
        (G.gaugeCover.cylinder j).toSpacetime
          ((lift (f (c, 0))).1, (lift (f (c, r))).2) :=
      (hright _ hrV).trans (hrecovery.symm.trans hmark)
    have hpair := (G.gaugeCover.cylinder j).embedding.injective hpoint
    have ht := congrArg Prod.fst hpair
    exact ht
  rw [htime] at hvel
  intro d
  exact D.prefixAction_fderiv_of_velocity hCoordinates hM12 hc R
    (E.square_extension (Z + r • W) c hsurvC hc.1)
    (E.square_euler (Z + r • W) c hsurvC hc.1) r hr
    (fun s hs => (hbase (hC.symm ▸ hs)).symm)
    (fun v _ => E.gamma_at_zero (Z + v • W)) _ hvel d

end PoincareConjecture.M14
