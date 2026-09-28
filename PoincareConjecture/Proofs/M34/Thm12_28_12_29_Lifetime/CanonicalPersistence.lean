import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceOrdinaryCap
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapAncientTransfer
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckAncientTransfer
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitCanonicalAlternatives

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M34

theorem exists_ordinary_canonical_persistence
    (P : RepairedKappaAlternativeTheory.{0}) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    ∃ c : ℝ, 0 < c ∧ ∀ {I : SpacetimeInterval}
      (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) I.domain)
      (R : OrdinaryProductRicciGeometry F.metric I),
      (∀ t ∈ I.domain, MetricComplete (F.metric t)) →
      let G := ordinaryChapter11Flow (I := I) (F := F) R
      ∀ (p : ℕ → G.point) (hp : ∀ k, 0 < G.scalar (p k))
        (hd : Tendsto (fun k => G.scalar (p k)) atTop atTop)
        (Conv : GeneralizedBlowupConvergence
          (fixedFlowBlowupSequence G p hp hd) (blowupBackwardInterval ⊤))
        {kappa : ℝ} (_K : M30AncientKappaIdentification Conv.limit kappa),
        ∀ᶠ k : ℕ in atTop, Nonempty (GeneralizedCanonicalControl (F := G)
          (p (Conv.subsequence k)).1 (p (Conv.subsequence k)).2 epsilon c) := by
  obtain ⟨delta0, hdelta0, hdelta0epsilon, hcap⟩ :=
    exists_ordinary_cap_persistence_accuracy.{0} hepsilon hsmall
  obtain ⟨epsilonPrime, hPrime, hclass⟩ := ordinaryChapter11_limit_neck_or_cap P
  let delta := min (delta0 / 2) (epsilonPrime / 2)
  have hdelta : 0 < delta :=
    lt_min (div_pos hdelta0 (by norm_num)) (div_pos hPrime (by norm_num))
  have hdelta0' : delta < delta0 :=
    (min_le_left _ _).trans_lt (by linarith)
  have hdeltaPrime : delta ≤ epsilonPrime :=
    (min_le_right _ _).trans (by linarith)
  have hdeltaepsilon : delta ≤ epsilon / 4 := hdelta0'.le.trans hdelta0epsilon
  obtain ⟨Craw, _hCraw, hcanonical⟩ := hclass delta hdelta hdeltaPrime
  let C := max 1 Craw
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  let c := capPersistenceConstant C (capBallVolumeCoefficient C)
  have hc : 0 < c :=
    (capPersistenceConstant_bounds hCpos.le (capBallVolumeCoefficient_pos hCpos)).1
  refine ⟨c, hc, ?_⟩
  intro I F R hcomplete
  dsimp only
  intro p hp hd Conv kappa K
  let : TopologicalSpace Conv.limit.carrier.carrier := Conv.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Conv.limit.carrier.carrier :=
    Conv.limit.carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ Conv.limit.carrier.carrier := Conv.limit.carrier.isManifold
  let : MeasurableSpace Conv.limit.carrier.carrier := Conv.limit.carrier.measurableSpace
  let : BorelSpace Conv.limit.carrier.carrier := Conv.limit.carrier.borelSpace
  let : T2Space Conv.limit.carrier.carrier := Conv.limit.carrier.t2Space
  let : T3Space Conv.limit.carrier.carrier := Conv.limit.carrier.t3Space
  let : SecondCountableTopology Conv.limit.carrier.carrier := Conv.limit.carrier.secondCountable
  let : ConnectedSpace Conv.limit.carrier.carrier := Conv.limit.connectedSpace
  rcases hcanonical F R p hp hd Conv K.certificate with hneck | hcapLimit
  · obtain ⟨N, hcenter⟩ := hneck
    have hhalf : epsilon < 1 / 2 := hsmall.trans_lt (by norm_num)
    filter_upwards [ordinaryChapter11_eventually_strongNeck_of_ancient
      R p hp hd Conv K N hcenter hepsilon hhalf hdeltaepsilon] with k hk
    obtain ⟨Ns, hNs⟩ := hk
    exact ⟨GeneralizedCanonicalControl.neck Ns hNs⟩
  · obtain ⟨N⟩ := hcapLimit
    obtain ⟨H, hHepsilon, hHC, hHD, hHbase⟩ :=
      exists_normalized_limit_cap_of_ancient Conv.limit K N
    have hHsmall : H.epsilon < delta0 := hHepsilon.trans_lt hdelta0'
    have hHC' : H.cap_constant ≤ C := hHC.trans (le_max_right _ _)
    filter_upwards [hcap C hC1 (EuclideanSpace ℝ (Fin 3)) I F R hcomplete
      p hp hd Conv H hHsmall hHC' hHD hHbase] with k hk
    obtain ⟨Hs, hHsepsilon, hHsc, hHsbase⟩ := hk
    exact ⟨ordinaryChapter11_canonicalControl_of_normalized_cap R
      (p (Conv.subsequence k)) (hp (Conv.subsequence k)) Hs hHsepsilon hHsc.le hHsbase⟩

end PoincareConjecture.M34
