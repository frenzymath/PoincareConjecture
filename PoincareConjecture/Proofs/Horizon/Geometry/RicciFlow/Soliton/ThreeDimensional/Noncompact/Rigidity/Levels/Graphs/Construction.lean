import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.ProductConvergence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)
  (B : G.NormalizedPotentialLimit L)
  {N : Type*} [TopologicalSpace N] [T3Space N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]

theorem exists_potentialLevelGraphs
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (h : RiemannianMetric 2 N)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.limitCarrier.carrier)
    (hpotential : ∀ z, B.potential (e z) = z.2)
    (hproduct : ∀ (z : N × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (L.limitFlow.metric 0).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
        h.inner z.1 v.1 w.1 + v.2 * w.2)
    (base : N) (hebase : e (base, 0) = L.base) :
    Nonempty (G.PotentialLevelGraphs L B h e base) := by
  classical
  let F : ℕ → ℝ × N → ℝ := fun k z =>
    G.normalizedPotentialPullback L (B.subsequence k) (e (z.2, z.1))
  let V : ℕ → Set (ℝ × N) := fun k =>
    {z | e (z.2, z.1) ∈ L.exhaustion (B.subsequence k)}
  have hswap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞
      (fun z : ℝ × N => e (z.2, z.1)) :=
    e.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hV (k : ℕ) : IsOpen (V k) := (L.exhaustion_open _).preimage hswap.continuous
  have hdomain := B.eventually_product_slab_domain G L e e.contMDiff 1
  have hsmooth : ∀ᶠ k in atTop,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (F k) (V k) ∧
        Icc (-1 : ℝ) 1 ×ˢ (univ : Set N) ⊆ V k := by
    filter_upwards [hdomain] with k hk
    refine ⟨(G.normalizedPotentialPullback_contMDiffOn L (B.subsequence k)).comp
      hswap.contMDiffOn (fun _ hx => hx), ?_⟩
    intro z hz
    exact hk z.2 z.1 hz.1
  have herr (δ : ℝ) (hδ : 0 < δ) :=
    B.eventually_product_slab_C1_error G L h e e.contMDiff hpotential hproduct 1 hδ
  obtain ⟨u, hroot, hu⟩ := Poincare.Manifold.exists_level_graphs_tendsto_C1
    F V hV (by norm_num : (0 : ℝ) < 1) h.tangentNorm hsmooth
    (fun δ hδ => (herr δ hδ).mono fun k hk y s hs => (hk y s hs).1)
    (fun δ hδ => (herr δ hδ).mono fun k hk y s hs =>
      (hk y s ⟨hs.1.le, hs.2.le⟩).2.1)
    (fun δ hδ => (herr δ hδ).mono fun k hk y s hs v =>
      (hk y s ⟨hs.1.le, hs.2.le⟩).2.2 v)
  have hscale := (G.normalizedPotentialPullback_scale_tendsto_atTop L hD p hescape).comp
    B.subsequence_strictMono.tendsto_atTop
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    (hroot.and (hdomain.and (hscale.eventually_gt_atTop 0)))
  let v : ℕ → N → ℝ := fun k => u (k + k₀)
  have hgood (k : ℕ) := hk₀ (k + k₀) (Nat.le_add_left _ _)
  have hv (k : ℕ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (v k) := (hgood k).1.1
  have hvmem (k : ℕ) (y : N) : v k y ∈ Ioo (-1) 1 := ((hgood k).1.2.1 y).1
  have hvroot (k : ℕ) (y : N) :
      G.normalizedPotentialPullback L (B.subsequence (k + k₀)) (e (y, v k y)) = 0 :=
    ((hgood k).1.2.1 y).2
  have hvbase (k : ℕ) : v k base = 0 := by
    have hzero : F (k + k₀) (0, base) = 0 := by
      change G.normalizedPotentialPullback L (B.subsequence (k + k₀)) (e (base, 0)) = 0
      rw [hebase, G.normalizedPotentialPullback_base]
    exact (((hgood k).1.2.2 base 0 (by constructor <;> norm_num)).mp hzero).symm
  have hmem (k : ℕ) (y : N) : e (y, v k y) ∈ L.exhaustion (B.subsequence (k + k₀)) :=
    (hgood k).2.1 y (v k y) ⟨(hvmem k y).1.le, (hvmem k y).2.le⟩
  let ψ : ℕ → N → M := fun k => G.potentialLevelGraphMap L B e (v k) (k + k₀)
  have hψ (k : ℕ) : ContMDiff (𝓡 2) (𝓡 3) ∞ (ψ k) := by
    intro y
    exact ((G.unscaledOriginalEmbedding_contMDiffOn L (B.subsequence (k + k₀))).contMDiffAt
      ((L.exhaustion_open _).mem_nhds (hmem k y))).comp y
        ((e.contMDiff (y, v k y)).comp y ((contMDiff_id.prodMk (hv k)) y))
  have hψinj (k : ℕ) : Injective (ψ k) := by
    intro x y hxy
    have heq := (G.unscaledOriginalEmbedding_injOn L (B.subsequence (k + k₀)))
      (hmem k x) (hmem k y) hxy
    exact congrArg Prod.fst (e.injective heq)
  have hψi (k : ℕ) (y : N) : Injective (mfderiv (𝓡 2) (𝓡 3) (ψ k) y) := by
    let E := G.unscaledOriginalEmbedding L (B.subsequence (k + k₀))
    let j : N → N × ℝ := fun z => (z, v k z)
    have hj : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ j := contMDiff_id.prodMk (hv k)
    have hE := (G.unscaledOriginalEmbedding_isLocalDiffeomorphOn L
      (B.subsequence (k + k₀))) ⟨e (y, v k y), hmem k y⟩
    have hE' : MDifferentiableAt (𝓡 3) (𝓡 3) E (e (j y)) :=
      hE.contMDiffAt.mdifferentiableAt (by simp)
    have hej : MDifferentiableAt (𝓡 2) (𝓡 3) (e ∘ j) y :=
      (e.contMDiff.comp hj).mdifferentiable (by simp) y
    have hcomp := mfderiv_comp y hE' hej
    change mfderiv (𝓡 2) (𝓡 3) (ψ k) y = _ at hcomp
    rw [hcomp]
    have hcomp' := mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) (j y))
      (hj.mdifferentiable (by simp) y)
    rw [hcomp']
    apply (hE.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    apply (e.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
    have hjd := mfderiv_prodMk mdifferentiableAt_id ((hv k).mdifferentiable (by simp) y)
    simp only [id_eq] at hjd
    change Injective (mfderiv (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z, v k z)) y)
    rw [hjd, mfderiv_id]
    intro a b hab
    exact congrArg Prod.fst hab
  let gseq : ℕ → RiemannianMetric 2 N := fun k =>
    RiemannianMetric.Induced.pullbackMetric S.metric (ψ k) (hψ k) (hψi k)
  have hinner (k : ℕ) (y : N) (a b : TangentSpace (𝓡 2) y) :
      (gseq k).inner y a b = S.metric.inner (ψ k y)
        (mfderiv (𝓡 2) (𝓡 3) (ψ k) y a) (mfderiv (𝓡 2) (𝓡 3) (ψ k) y b) := rfl
  have hvsmall (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ k in atTop,
      (∀ y, |v k y| ≤ δ) ∧ ∀ y (a : TangentSpace (𝓡 2) y),
        |mvfderiv (𝓡 2) (v k) y a| ≤ δ * h.tangentNorm y a :=
    (tendsto_add_atTop_nat k₀).eventually (hu δ hδ)
  have hambient (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop,
      ∀ y (a : TangentSpace (𝓡 2) y),
        |(gseq k).inner y a a - (h.inner y a a + (mvfderiv (𝓡 2) (v k) y a) ^ 2)| ≤
          ε * (h.inner y a a + (mvfderiv (𝓡 2) (v k) y a) ^ 2) := by
    let K := e '' (univ ×ˢ Icc (-1 : ℝ) 1)
    have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image e.continuous
    filter_upwards [(B.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat k₀)).eventually
      (G.unscaledOriginalEmbedding_eventually_relative_metric_error L K hK hε)] with k hk
    intro y a
    let j : N → L.limitCarrier.carrier := fun z => e (z, v k z)
    have hj : ContMDiff (𝓡 2) (𝓡 3) ∞ j := e.contMDiff.comp (contMDiff_id.prodMk (hv k))
    have hpoint : j y ∈ K := ⟨(y, v k y), ⟨mem_univ _,
      ⟨(hvmem k y).1.le, (hvmem k y).2.le⟩⟩, rfl⟩
    have hcomp := mfderiv_comp y
      (((G.unscaledOriginalEmbedding_contMDiffOn L (B.subsequence (k + k₀))).contMDiffAt
        ((L.exhaustion_open _).mem_nhds (hmem k y))).mdifferentiableAt (by simp))
      (hj.mdifferentiable (by simp) y)
    have hprod := h.product_metric_height_graph_inner (L.limitFlow.metric 0) e hproduct (hv k) y a
    have hh := hk.2 (j y) hpoint (mfderiv (𝓡 2) (𝓡 3) j y a)
    rw [hinner]
    change mfderiv (𝓡 2) (𝓡 3) (ψ k) y = _ at hcomp
    rw [hcomp]
    change |S.metric.inner _ _ _ - _| ≤ _
    rw [← hprod]
    exact hh
  refine ⟨{
    offset := k₀
    height := v
    height_contMDiff := hv
    height_mem := hvmem
    height_base := hvbase
    graph_mem := hmem
    graph_level := ?_
    graph_contMDiff := hψ
    graph_injective := hψinj
    graph_immersion := hψi
    metric := gseq
    metric_inner := hinner
    height_tendsto_C1 := hvsmall
    area_tendsto := h.tendsto_area_of_height_graph_metric_error gseq v hambient
      (fun η hη => (hvsmall η hη).mono fun _ hk => hk.2)
  }⟩
  intro k y
  exact (G.normalizedPotentialPullback_eq_zero_iff L (B.subsequence (k + k₀))
    (hgood k).2.2.ne' (e (y, v k y))).mp (hvroot k y)

end PoincareConjecture.ShrinkingSolitonFlow
