import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.JetSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace NormalizedKappaSpacetimeEmbedding

variable {kappa : ℝ} {source target : BasedKappaSolution kappa}
  {U : Set target.carrier.carrier}


theorem terminal_chart_map_regular
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (Iic 0 ×ˢ U))
    (hU : IsOpen U) (q : target.carrier.carrier)
    {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target)
    (hx : (extChartAt (𝓡 3) q).symm z ∈ U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y ↦ (e.toFun (0, (extChartAt (𝓡 3) q).symm y)).2) z ∧
      Function.Injective (mfderiv (𝓡 3) (𝓡 3)
        (fun y ↦ (e.toFun (0, (extChartAt (𝓡 3) q).symm y)).2) z) := by
  let c := extChartAt (𝓡 3) q
  let f := fun x ↦ (e.toFun (0, x)).2
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hz).contMDiffAt
    (extChartAt_target_mem_nhds' hz)
  have hf := e.spatial_contMDiffAt hU (show (0 : ℝ) ∈ Iic 0 by simp) hx
  refine ⟨hf.comp z hc, ?_⟩
  change Function.Injective (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) z)
  rw [mfderiv_comp z (hf.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hz
  exact (e.spatial_mfderiv_injective hU (show (0 : ℝ) ∈ Iic 0 by simp) hx).comp hi.injective



private theorem terminal_coefficient_eq_terminal_pullback
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (Iic 0 ×ˢ U))
    (hU : IsOpen U)
    (hfixed : ∀ t : ℝ, t ≤ 0 → ∀ x ∈ U,
      (e.toFun (t, x)).2 = (e.toFun (0, x)).2)
    (q : target.carrier.carrier) (a b : Fin 3)
    {t : ℝ} (ht : t ≤ 0) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target)
    (hx : (extChartAt (𝓡 3) q).symm z ∈ U) :
    normalizedKappaPullbackCoefficient e q a b (t, z) =
      (source.flow.flow.metric t).pullbackCoefficients
        (fun y ↦ (e.toFun (0, (extChartAt (𝓡 3) q).symm y)).2) z
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  exact e.terminal_coefficient_eq_fixed_pullback hU
    (fun s t x hx hs ht ↦ (hfixed s hs x hx).trans (hfixed t ht x hx).symm)
    q a b ht hz hx

end NormalizedKappaSpacetimeEmbedding

namespace M23TerminalMetricConvergence


theorem terminal_spatial_jet_eq
    {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 < ρ)
    (f : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Iic 0 ×ˢ closedBall x₀ ρ))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball x₀ ρ) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y ↦ f (0, y)) x =
      (M23TerminalMetricJet r f (0, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) := by
  have hset : Iic (0 : ℝ) ×ˢ closedBall x₀ ρ =ᶠ[𝓝 (0, x)]
      Iic 0 ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3))) := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (isOpen_ball.mem_nhds hx)] with w hw
    apply propext
    change (w.1 ≤ 0 ∧ w.2 ∈ closedBall x₀ ρ) ↔ (w.1 ≤ 0 ∧ True)
    simp only [ball_subset_closedBall hw, and_true]
  dsimp only [M23TerminalMetricJet]
  rw [← iteratedFDerivWithin_congr_set hset r]
  exact AncientCompactness.iteratedFDeriv_spatial_slice_of_centered_halfCylinder
    hρ f hf le_rfl hx r


theorem terminal_spatial_jet_eq_of_eqOn
    {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 < ρ)
    (f g : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ)
    (hfg : EqOn f g (Iic 0 ×ˢ closedBall x₀ ρ))
    (hg : ContDiffOn ℝ ∞ g (Iic 0 ×ˢ closedBall x₀ ρ))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball x₀ ρ) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y ↦ g (0, y)) x =
      (M23TerminalMetricJet r f (0, x)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) := by
  have hset : Iic (0 : ℝ) ×ˢ closedBall x₀ ρ =ᶠ[𝓝 (0, x)]
      Iic 0 ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3))) := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (isOpen_ball.mem_nhds hx)] with w hw
    apply propext
    change (w.1 ≤ 0 ∧ w.2 ∈ closedBall x₀ ρ) ↔ (w.1 ≤ 0 ∧ True)
    simp only [ball_subset_closedBall hw, and_true]
  dsimp only [M23TerminalMetricJet]
  have hxΩ : (0, x) ∈ Iic (0 : ℝ) ×ˢ closedBall x₀ ρ :=
    ⟨mem_Iic.mpr le_rfl, ball_subset_closedBall hx⟩
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) hfg hxΩ r
  rw [← iteratedFDerivWithin_congr_set hset r, he]
  exact AncientCompactness.iteratedFDeriv_spatial_slice_of_centered_halfCylinder
    hρ g hg le_rfl hx r

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem tendstoUniformlyOn_terminal_spatialJet_on_closedBall
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (q : G.limit.carrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ}
    (hρ : 0 < ρ) (hchart : closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target)
    (r : ℕ) (a b : Fin 3) :
    TendstoUniformlyOn
      (fun k ↦ iteratedFDeriv ℝ r (fun z ↦
        ((S.term (G.subsequence k)).flow.flow.metric 0).pullbackCoefficients
          (fun y ↦ ((e k).toFun (0, (extChartAt (𝓡 3) q).symm y)).2) z
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
      (iteratedFDeriv ℝ r (fun z ↦
        (G.limit.flow.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm z
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
      atTop (closedBall x₀ (ρ / 2)) := by
  let c := extChartAt (𝓡 3) q
  let Ω : Set (ℝ × EuclideanSpace ℝ (Fin 3)) := Iic 0 ×ˢ closedBall x₀ ρ
  let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) ↦
    ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
      (fun y ↦ ((e k).toFun (0, c.symm y)).2) z.2
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  let g := fun z : ℝ × EuclideanSpace ℝ (Fin 3) ↦
    (G.limit.flow.flow.metric z.1).pullbackCoefficients c.symm z.2
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  let gs := G.limit.carrier.coordinateCoefficient q
    (fun t x v w ↦ (G.limit.flow.flow.metric t).inner x v w) a b
  have hg : ContDiffOn ℝ ∞ g Ω := by
    exact ((((G.limit.flow.flow.contDiffOn_pullbackCoefficients_within
      (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm (n := ∞) q)).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const).mono (prod_mono subset_rfl hchart))
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((isCompact_closedBall x₀ ρ).image_of_continuousOn
      ((continuousOn_extChartAt_symm q).mono hchart))
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  have hf (k : ℕ) (hk : j ≤ k) : ContDiffOn ℝ ∞ (f k) Ω := by
    let W := c.target ∩ c.symm ⁻¹' G.exhaustion k
    have hW : IsOpen W :=
      (continuousOn_extChartAt_symm q).isOpen_inter_preimage
        (isOpen_extChartAt_target q) (G.exhaustion_open k)
    have hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞
        (fun y ↦ ((e k).toFun (0, c.symm y)).2) W := fun y hy ↦
      ((e k).terminal_chart_map_regular (G.exhaustion_open k) q hy.1 hy.2).1.contMDiffWithinAt
    apply ((((S.term (G.subsequence k)).flow.flow.contDiffOn_pullbackCoefficients_within
      hW hs).clm_apply contDiffOn_const).clm_apply contDiffOn_const).mono
    exact prod_mono subset_rfl (fun y hy ↦
      ⟨hchart hy, hmono hk (hj (mem_image_of_mem _ hy))⟩)
  have heq (k : ℕ) (hk : j ≤ k) :
      EqOn (normalizedKappaPullbackCoefficient (e k) q a b) (f k) Ω := by
    intro z hz
    exact (e k).terminal_coefficient_eq_terminal_pullback (G.exhaustion_open k) (hfixed k)
      q a b hz.1 (hchart hz.2) (hmono hk (hj (mem_image_of_mem _ hz.2)))
  have hsmall : closedBall x₀ (ρ / 2) ⊆ ball x₀ ρ := closedBall_subset_ball (by linarith)
  have hjets : TendstoUniformlyOn
      (fun k z ↦ M23TerminalMetricJet r (normalizedKappaPullbackCoefficient (e k) q a b) (0, z))
      (fun z ↦ M23TerminalMetricJet r gs (0, z)) atTop (closedBall x₀ (ρ / 2)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, _, hN⟩ := hconv q j r ({0} ×ˢ closedBall x₀ (ρ / 2))
      (isCompact_singleton.prod (isCompact_closedBall _ _))
      (fun z hz ↦ ⟨(mem_singleton_iff.mp hz.1).le,
        hchart (ball_subset_closedBall (hsmall hz.2)),
        hj (mem_image_of_mem _ (ball_subset_closedBall (hsmall hz.2)))⟩) ε hε
    filter_upwards [eventually_ge_atTop N] with k hk z hz
    simpa only [dist_eq_norm, norm_sub_rev] using hN k hk a b (0, z) ⟨mem_singleton 0, hz⟩
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r ↦
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
  have hrestrict := P.uniformContinuous.comp_tendstoUniformlyOn hjets
  have htarget := hrestrict.congr_right (fun z hz ↦
    (terminal_spatial_jet_eq hρ g hg (hsmall hz) r).symm)
  apply htarget.congr
  filter_upwards [eventually_ge_atTop j] with k hk z hz
  exact (terminal_spatial_jet_eq_of_eqOn hρ _ (f k) (heq k hk) (hf k hk) (hsmall hz) r).symm



theorem eventually_terminal_chart_domain (q : G.limit.carrier.carrier)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    ∀ᶠ z : ℕ × EuclideanSpace ℝ (Fin 3) in atTop ×ˢ 𝓝 p,
      z.2 ∈ (extChartAt (𝓡 3) q).target ∧
        (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion z.1 := by
  let c := extChartAt (𝓡 3) q
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_singleton (x := c.symm p))
  let W := c.target ∩ c.symm ⁻¹' G.exhaustion j
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) (G.exhaustion_open j)
  have hpW : p ∈ W := ⟨hp, hj (mem_singleton _)⟩
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [(eventually_ge_atTop j).prod_mk (hW.mem_nhds hpW)] with z hz
  exact ⟨hz.2.1, hmono hz.1 hz.2.2⟩



theorem tendsto_terminal_spatialJet_prod
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (q : G.limit.carrier.carrier) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (extChartAt (𝓡 3) q).target) (r : ℕ) (a b : Fin 3) :
    Tendsto (fun z : ℕ × EuclideanSpace ℝ (Fin 3) ↦ iteratedFDeriv ℝ r (fun y ↦
      ((S.term (G.subsequence z.1)).flow.flow.metric 0).pullbackCoefficients
        (fun w ↦ ((e z.1).toFun (0, (extChartAt (𝓡 3) q).symm w)).2) y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) z.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (iteratedFDeriv ℝ r (fun y ↦
        (G.limit.flow.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)) := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds' hp)
  have hρ : 0 < R / 2 := by positivity
  have hchart : closedBall p (R / 2) ⊆ (extChartAt (𝓡 3) q).target :=
    (closedBall_subset_ball (by linarith)).trans hsub
  have hu := hconv.tendstoUniformlyOn_terminal_spatialJet_on_closedBall hfixed q hρ hchart r a b
  have hulift : TendstoUniformlyOn
      (fun z : ℕ × EuclideanSpace ℝ (Fin 3) ↦ iteratedFDeriv ℝ r (fun y ↦
        ((S.term (G.subsequence z.1)).flow.flow.metric 0).pullbackCoefficients
          (fun w ↦ ((e z.1).toFun (0, (extChartAt (𝓡 3) q).symm w)).2) y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
      (iteratedFDeriv ℝ r (fun y ↦
        (G.limit.flow.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)))
      (atTop ×ˢ 𝓝 p) (closedBall p (R / 2 / 2)) :=
    fun V hV ↦ tendsto_fst.eventually (hu V hV)
  have hs := (((G.limit.flow.flow.metric 0).contDiffAt_pullbackCoefficients
    ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hp).contMDiffAt
      (extChartAt_target_mem_nhds' hp))).clm_apply
        (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))).clm_apply
          (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  apply hulift.tendsto_comp (hs.continuousAt_iteratedFDeriv
    (by exact_mod_cast le_top : (r : ℕ∞ω) ≤ ∞)).continuousWithinAt
  rw [nhdsWithin_eq_nhds.mpr (closedBall_mem_nhds p (by positivity : 0 < R / 2 / 2))]
  exact tendsto_snd

end M23TerminalMetricConvergence

end PoincareConjecture
