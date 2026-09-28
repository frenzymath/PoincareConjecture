import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_EndpointRecovery
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_68_ActionContact

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

theorem minimizing_exponential_limit
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {Zs : ℕ → G.Horizontal x} {Z : G.Horizontal x}
    (hlim : Tendsto Zs atTop (𝓝 Z))
    (hZs : ∀ k, (Zs k, Real.sqrt tau) ∈ E.domain)
    (hmins : ∀ k, M14IsMinimizing
      (E.path (Zs k) (Real.sqrt tau) (hZs k) (Real.sqrt_pos.mpr htau)))
    (hZ : (Z, Real.sqrt tau) ∈ E.domain)
    (htime : T - tau ∈ interior I.domain)
    (hattained : ∃ p : M14BackwardPath G T 0 tau x
      (survivalSliceMap E tau htau.le q0 Z).val, M14IsMinimizing p) :
    M14IsMinimizing (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let f := survivalSliceMap E tau htau.le q0
  obtain ⟨p, hp⟩ := hattained
  obtain ⟨W, hW, htrace, _⟩ := minimizing_exponential_branch LG E p hp
  obtain ⟨V, hV, hqV, cost, hcost, hcenter, hpaths⟩ :=
    smooth_action_recovery_of_represented_path hM12 E p hW htrace htime
  have hf : ContinuousAt f Z := (survivalSliceMap_smooth E htau.le q0 hZ).continuousAt
  have hend : Tendsto (fun k => f (Zs k)) atTop (𝓝 (f Z)) := hf.tendsto.comp hlim
  have haction : Tendsto (fun k => E.action (Zs k) (Real.sqrt tau)) atTop
      (𝓝 (E.action Z (Real.sqrt tau))) :=
    ((LG.exponential.action_differential T x E).2 Z (Real.sqrt tau) hZ
      (Real.sqrt_pos.mpr htau)).1.continuousAt.tendsto.comp hlim
  have hcostlim : Tendsto (fun k => cost (f (Zs k))) atTop (𝓝 (cost (f Z))) :=
    ((hcost _ hqV).continuousWithinAt.continuousAt (hV.mem_nhds hqV)).tendsto.comp hend
  have hle : ∀ᶠ k in atTop, E.action (Zs k) (Real.sqrt tau) ≤ cost (f (Zs k)) := by
    filter_upwards [hend.eventually (hV.mem_nhds hqV)] with k hk
    obtain ⟨r, hr⟩ := hpaths (f (Zs k)) hk
    have hfinite : M14FiniteValueDomain G T 0 tau x (f (Zs k)).val := by
      have h := M14.finiteValueDomain_of_minimizing
        (E.path (Zs k) (Real.sqrt tau) (hZs k) (Real.sqrt_pos.mpr htau)) (hmins k)
      rwa [Real.sq_sqrt htau.le, ← survivalSliceMap_val E htau.le q0 (hZs k)] at h
    calc
      E.action (Zs k) (Real.sqrt tau) = M14ActionValue G T 0 tau x (f (Zs k)).val :=
        minimizing_survival_action_eq E htau q0 (hZs k) (hmins k)
      _ ≤ M14BackwardLAction G r := M14.actionValue_le_action hfinite r
      _ = cost (f (Zs k)) := hr
  have hlimit := le_of_tendsto_of_tendsto haction hcostlim hle
  have hfinite := M14.finiteValueDomain_of_minimizing p hp
  have heq : E.action Z (Real.sqrt tau) = M14ActionValue G T 0 tau x (f Z).val := by
    apply le_antisymm
    · exact hlimit.trans_eq (hcenter.trans (M14.action_eq_actionValue_of_minimizing p hp))
    · exact actionValue_le_survival_action E htau q0 hZ hfinite
  have hfinite' : M14FiniteValueDomain G T 0 ((Real.sqrt tau) ^ 2) x
      (E.gamma Z (Real.sqrt tau)) := by
    rw [Real.sq_sqrt htau.le, ← survivalSliceMap_val E htau.le q0 hZ]
    exact hfinite
  apply (M14.isMinimizing_iff_action_eq_actionValue hfinite' _).mpr
  rw [← E.action_eq Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau),
    Real.sq_sqrt htau.le, ← survivalSliceMap_val E htau.le q0 hZ]
  exact heq

end PoincareConjecture.Proofs.M46
