import PoincareConjecture.Proofs.M14.Sec6_2_SquareVariationRestriction

set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem exists_parameterLineVariation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (R : M14SquareRootPath G p) (γ : ℝ × P → G.Point) {C : Set ℝ} {U : Set P}
    (hU : IsOpen U)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ γ (C ×ˢ U))
    (hsub : M14SqrtParameterInterval a b ⊆ C)
    (hclock : ∀ s ∈ C, ∀ z ∈ U, G.spacetime.timeFunction (γ (s, z)) = T - s ^ 2)
    (z d : P) (hz : z ∈ U)
    (hzero : ∀ s ∈ M14SqrtParameterInterval a b, γ (s, z) = R.curve s) :
    ∃ V : M14LVariationData G p R,
      (∀ u ∈ V.parameterDomain, z + u • d ∈ U) ∧
      ∀ s ∈ M14SqrtParameterInterval a b, ∀ u, V.squareFamily s u = γ (s, z + u • d) := by
  have hline : ContDiff ℝ ∞ (fun u : ℝ => z + u • d) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hnear : {u : ℝ | z + u • d ∈ U} ∈ 𝓝 0 :=
    (hU.preimage hline.continuous).mem_nhds (by
      change z + (0 : ℝ) • d ∈ U
      simpa only [zero_smul, add_zero] using hz)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hparam (u : ℝ) (hu : u ∈ Ioo (-ρ) ρ) : z + u • d ∈ U := by
    apply hρsub
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hu
  let H := fun w : ℝ × ℝ => γ (w.1, z + w.2 • d)
  have hk : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) ∞ (fun w : ℝ × ℝ => (w.1, z + w.2 • d)) := by
    rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod,
      chartedSpaceSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_fst.prodMk (contDiff_const.add (contDiff_snd.smul contDiff_const))).contMDiff
  have hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ H
      (M14SqrtParameterInterval a b ×ˢ Ioo (-ρ) ρ) :=
    hγ.comp hk.contMDiffOn (fun w hw => ⟨hsub hw.1, hparam w.2 hw.2⟩)
  have htime (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b)
      (u : ℝ) (hu : u ∈ Ioo (-ρ) ρ) : G.spacetime.timeFunction (H (s, u)) = T - s ^ 2 :=
    hclock s (hsub hs) _ (hparam u hu)
  have hbase (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b) : H (s, 0) = R.curve s := by
    simpa only [H, zero_smul, add_zero] using hzero s hs
  obtain ⟨V, hVparam, hV⟩ := exists_variationOfSquare_eqOn hM12 R H hρ hH htime hbase
  exact ⟨V, fun u hu => hparam u (hVparam ▸ hu), hV⟩

end PoincareConjecture.M14
