import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.ScalarSpacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.Diffeomorphisms
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Convergence.Spectrum
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaRoundness

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

theorem round_curvature_contractions
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hround : ConstantPositiveSectionalCurvature g D) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : M,
      D.scalarCurvature x = 6 * r ∧ D.curvatureTensorNorm x ^ 2 = 12 * r ^ 2 := by
  obtain ⟨r, hr, hsec⟩ := hround
  refine ⟨r, hr, fun x => ?_⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨b, hsym, hmetric, hunit, hpair, k, e, horder, heigen, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_operator_spectrum hD x
  have hk (i : Fin 3) : k i = r := by
    obtain ⟨u, v, huv, hW⟩ := hunit (e i) (e.orthonormal.1 i)
    have hsection := hsec x u v huv.1 huv.2.1 huv.2.2
    have hcurv := hpair u v u v
    rw [hW, heigen, inner_smul_right, e.inner_eq_ite, if_pos rfl, mul_one] at hcurv
    have hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 1 := by
      rw [huv.1, huv.2.1, huv.2.2]
      norm_num
    unfold LeviCivitaData.sectionalCurvature at hsection
    rw [hgram, div_one, hcurv] at hsection
    exact hsection
  rw [hscalar, hnorm, hk, hk, hk]
  constructor <;> ring

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem eventually_rescaling_ricciComplement_mem
    (G : AncientCompactTimeConvergence S)
    (hcompact : CompactSpace G.limit.carrier.carrier)
    (hcalculus : ∀ k, ((S.rescaling (G.subsequence k)).flow.connection (-1)).CurvatureTensorCalculus)
    (hlimit : (G.limit.flow.connection (-1)).CurvatureTensorCalculus)
    (hround : ConstantPositiveSectionalCurvature
      (G.limit.flow.metric (-1)) (G.limit.flow.connection (-1)))
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ k in atTop, ∀ x : M,
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨((S.rescaling (G.subsequence k)).flow.metric (-1)).toRiemannianMetric⟩
      ((S.rescaling (G.subsequence k)).flow.connection (-1)).ricciComplementTensor
        (hcalculus k) x ∈ tensorPinchingCone c := by
  let : CompactSpace G.limit.carrier.carrier := hcompact
  let : PreconnectedSpace G.limit.carrier.carrier :=
    ⟨G.limit.carrier.connected.isPreconnected⟩
  let : Nonempty G.limit.carrier.carrier := ⟨Classical.choose G.limit.carrier.connected.nonempty⟩
  let : ConnectedSpace G.limit.carrier.carrier := ⟨inferInstance⟩
  obtain ⟨r, hr, hcontractions⟩ := round_curvature_contractions
    (G.limit.flow.connection (-1)) hlimit hround
  let P (k : ℕ) (p : G.limit.carrier.carrier) : Prop :=
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨((S.rescaling (G.subsequence k)).flow.metric (-1)).toRiemannianMetric⟩
    ((S.rescaling (G.subsequence k)).flow.connection (-1)).ricciComplementTensor
      (hcalculus k) ((G.embedding k).toFun (-1, p)).2 ∈ tensorPinchingCone c
  have hlocal (p : G.limit.carrier.carrier) :
      ∃ U ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ q ∈ U, P k q := by
    have hs := (G.tendsto_scalarCurvature_prod (-1, p) (by norm_num)).comp
      (tendsto_fst.prodMk (tendsto_const_nhds.prodMk_nhds tendsto_snd))
    have hn := (G.tendsto_curvatureTensorNorm_prod (-1, p) (by norm_num)).comp
      (tendsto_fst.prodMk (tendsto_const_nhds.prodMk_nhds tendsto_snd))
    have hns := hn.pow 2
    rw [(hcontractions p).1] at hs
    rw [(hcontractions p).2] at hns
    have he := eventually_ricciComplement_mem_of_round_contractions
      (D := fun z : ℕ × G.limit.carrier.carrier =>
        (S.rescaling (G.subsequence z.1)).flow.connection (-1))
      (fun z => hcalculus z.1) (fun z => ((G.embedding z.1).toFun (-1, z.2)).2)
      hr hs hns hc
    change ∀ᶠ z : ℕ × G.limit.carrier.carrier in atTop ×ˢ 𝓝 p, P z.1 z.2 at he
    obtain ⟨A, hA, B, hB, hAB⟩ := eventually_prod_iff.mp he
    exact ⟨{q | B q}, hB, hA.mono (fun k hk q hq => hAB hk hq)⟩
  classical
  choose U hU hlate using hlocal
  have hC : IsCompact (univ : Set G.limit.carrier.carrier) := isCompact_univ
  obtain ⟨s, hs⟩ := hC.elim_nhds_subcover' (fun p _ => U p) (fun p _ => hU p)
  have hall : ∀ᶠ k in atTop, ∀ p, P k p := by
    filter_upwards [s.eventually_all.mpr (fun p _ => hlate p.1)] with k hk p
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs (mem_univ p))
    exact hk q hq p hpq
  filter_upwards [hall, G.eventually_exists_spatialDiffeomorph hcompact] with k hk hφ x
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨p, rfl⟩ := φ.surjective x
  have hh := hk p
  dsimp only [P] at hh
  rw [← hφ p] at hh
  exact hh

end PoincareConjecture.AncientKappaRoundness
