import PoincareConjecture.Proofs.M14.Sec6_3_InitialVectorVariation
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

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

theorem exponentialLine_contMDiffOn (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {b : ℝ} {U : Set ℝ}
    (hsurv : ∀ r ∈ U, (Z + r • W, b) ∈ E.domain) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1) (Icc 0 b ×ˢ U) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hk : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (Z + z.2 • W, z.1)) :=
    (contDiff_const.add (contDiff_snd.smul contDiff_const)).prodMk contDiff_fst
  have hkM : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × ℝ => (Z + z.2 • W, z.1)) := by
    rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod,
      chartedSpaceSelf_prod, chartedSpaceSelf_prod]
    exact hk.contMDiff
  exact E.family_smooth.comp hkM.contMDiffOn
    (fun z hz => (E.maximal_lifetime _).out (E.domain_zero _) (hsurv z.2 hz.2) hz.1)

theorem exponentialLine_contMDiffAt (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {b c r : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hsurv : ∀ v ∈ U, (Z + v • W, b) ∈ E.domain)
    (hc : c ∈ Ioo 0 b) (hr : r ∈ U) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1) (c, r) := by
  apply (exponentialLine_contMDiffOn E Z W hsurv (c, r)
    ⟨Ioo_subset_Icc_self hc, hr⟩).contMDiffAt
  exact mem_of_superset ((isOpen_Ioo.prod hU).mem_nhds ⟨hc, hr⟩)
    (fun _ hz => ⟨Ioo_subset_Icc_self hz.1, hz.2⟩)

theorem exponentialLine_gauge_coordinate_velocity_contDiffAt
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x)
    {b c r : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hsurv : ∀ v ∈ U, (Z + v • W, b) ∈ E.domain)
    (hc : c ∈ Ioo 0 b) (hr : r ∈ U) (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j)
    (hlift : ContMDiffAt (spacetimeModel n) (spacetimeModel n) ∞ lift
      (E.gamma (Z + r • W) c)) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (lift (E.gamma (Z + z.2 • W) z.1)).2.val) (c, r) ∧
    ContDiffAt ℝ ∞ (fun v => deriv (fun s => (lift (E.gamma (Z + v • W) s)).2.val) c) r := by
  have hF := exponentialLine_contMDiffAt E Z W hU hsurv hc hr
  have hL := hlift.comp (c, r) hF
  have hq : ContDiffAt ℝ ∞
      (fun z : ℝ × ℝ => (lift (E.gamma (Z + z.2 • W) z.1)).2.val) (c, r) := by
    have h := (contMDiff_subtype_val.contMDiffAt.comp (c, r)
      (contMDiff_snd.contMDiffAt.comp (c, r) hL))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt
  refine ⟨hq, ?_⟩
  have hswap : ContDiffAt ℝ ∞
      (fun z : ℝ × ℝ => (lift (E.gamma (Z + z.1 • W) z.2)).2.val) (r, c) := by
    have hk : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (z.2, z.1)) (r, c) :=
      contDiffAt_snd.prodMk contDiffAt_fst
    have h := hq.comp (r, c) hk
    exact h
  have hd : ContDiffAt ℝ ∞
      (fun v => fderiv ℝ (fun s => (lift (E.gamma (Z + v • W) s)).2.val) c) r :=
    hswap.fderiv (g := fun _ => c) contDiffAt_const (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))

end PoincareConjecture.M14
