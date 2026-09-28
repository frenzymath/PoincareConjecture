import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSlices
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector
import PoincareConjecture.Proofs.M14.Sec6_2_SquareVariationRestriction











set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space





theorem exists_initialVectorVariation
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x) {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    ∃ V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos),
      (∀ u ∈ V.parameterDomain, (Z + u • W, s) ∈ E.domain) ∧
      ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
        V.squareFamily r u = E.gamma (Z + u • W) r := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨U, hU, hZU, htube, hsm⟩ := exponentialFamily_smooth_prefix hM04 hM12 E hs hpos
  have hline : ContDiff ℝ ∞ (fun u : ℝ => Z + u • W) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hnear : {u : ℝ | Z + u • W ∈ U} ∈ 𝓝 0 :=
    (hU.preimage hline.continuous).mem_nhds (by
      change Z + (0 : ℝ) • W ∈ U
      simpa only [zero_smul, add_zero] using hZU)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hparam (u : ℝ) (hu : u ∈ Ioo (-ρ) ρ) : Z + u • W ∈ U := by
    apply hρsub
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using hu
  have hC : M14SqrtParameterInterval 0 (s ^ 2) = Icc 0 s := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le]
  let H : ℝ × ℝ → G.Point := fun z => E.gamma (Z + z.2 • W) z.1
  have hk : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (Z + z.2 • W, z.1)) :=
    (contDiff_const.add (contDiff_snd.smul contDiff_const)).prodMk contDiff_fst
  have hkM : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × ℝ => (Z + z.2 • W, z.1)) := by
    rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod,
      chartedSpaceSelf_prod, chartedSpaceSelf_prod]
    exact hk.contMDiff
  have hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval 0 (s ^ 2) ×ˢ Ioo (-ρ) ρ) :=
    hsm.comp hkM.contMDiffOn (fun z hz => ⟨hparam z.2 hz.2, hC ▸ hz.1⟩)
  have hclock (r : ℝ) (hr : r ∈ M14SqrtParameterInterval 0 (s ^ 2))
      (u : ℝ) (hu : u ∈ Ioo (-ρ) ρ) : G.spacetime.timeFunction (H (r, u)) = T - r ^ 2 :=
    E.clock _ _ (htube ⟨hparam u hu, hC ▸ hr⟩)
  have hzero (r : ℝ) (hr : r ∈ M14SqrtParameterInterval 0 (s ^ 2)) :
      H (r, 0) = (E.square_path Z s hs hpos).curve r := by
    simpa only [H, zero_smul, add_zero] using (exponential_square_curve_eq E Z hs hpos hr).symm
  obtain ⟨V, hVparam, hV⟩ :=
    exists_variationOfSquare_eqOn hM12 (E.square_path Z s hs hpos) H hρ hH hclock hzero
  refine ⟨V, ?_, hV⟩
  intro u hu
  exact htube ⟨hparam u (hVparam ▸ hu), hpos.le, le_rfl⟩

end PoincareConjecture.M14
