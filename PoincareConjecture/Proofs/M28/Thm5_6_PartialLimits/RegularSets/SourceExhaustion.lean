import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.QuotientConnectedness
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactExhaustion
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.SourceCoreCoverage
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.Exhaustion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.FlowCarrier












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u

namespace PoincareConjecture.M28




theorem exists_regular_pointed_source_exhaustion
    {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    [Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → RegularNormalChartCover (g k) (p k)
      (δ j) (R j) (ρ j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j)
    (hstep : ∀ j, 4 * δ (j + 1) ≤ 2 * δ j)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {D : ∀ _i _j : ℕ, C(ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×
      ball (0 : EuclideanSpace ℝ (Fin n)) 1, ℝ)}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ×
        ball (0 : EuclideanSpace ℝ (Fin n)) 1) =>
        dist (regularUnitBallMap cover (φ k) i x.1)
          (regularUnitBallMap cover (φ k) j x.2)) (D i j) atTop)
    (L : ℕ → ℝ≥0)
    (he : ∀ k i, LipschitzWith (L i) (regularUnitBallMap cover (φ k) i))
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤
      dist (regularUnitBallMap cover (φ k) i x) (regularUnitBallMap cover (φ k) i y))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hbound : ∀ i j, LocallyEventuallyBoundedDerivatives
      (Subtype.val '' ChartDistance.overlap (fun i j => D i j) i j)
      (fun k => ChartDistance.coordinateRepresentative (fun _ : ℕ => ball 0 1)
        (fun _ => isOpen_ball) (i := i) (j := j)
          (fun x => Function.invFun (regularUnitBallMap cover (φ k) j)
            (regularUnitBallMap cover (φ k) i x)))) :
    letI : LocallyCompactSpace (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      isOpen_ball.locallyCompactSpace
    let O := ChartDistance.overlapSystem (fun l q x y =>
      (hD l q).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y)))
      L he c hc hlower
      (fun k i => regularUnitBallMap_isOpenEmbedding cover hρ hρR (φ k) i)
      (fun k => hconn (φ k))
    letI := quotientChartedSpace (fun _ : ℕ => ball 0 1) (fun _ => isOpen_ball) O
    ConnectedSpace (Quotient O.setoid) ∧
    ∃ E : ℕ → Set (Quotient O.setoid),
      (∀ j, IsOpen (E j)) ∧ (∀ j, IsConnected (E j)) ∧
      (∀ j, O.include 0 ⟨0, by simp⟩ ∈ E j) ∧
      (∀ j, IsCompact (closure (E j))) ∧
      (∀ j, closure (E j) ⊆ E (j + 1)) ∧ (⋃ j, E j) = univ ∧
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ F : ∀ j, Quotient O.setoid → M (φ (σ j)),
      (∀ j, Topology.IsOpenEmbedding (fun x : E j => F j x) ∧
        IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F j) (E j) ∧
        F j (O.include 0 ⟨0, by simp⟩) = p (φ (σ j))) ∧
      (∀ i C, IsCompact C → TendstoUniformlyOn
        (fun j x => dist (F j (O.include i x))
          (regularUnitBallMap cover (φ (σ j)) i x)) (fun _ => 0) atTop C) ∧
      (∀ i m B, IsCompact B → B ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
        TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m
          (ChartDistance.coordinateRepresentative (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (j := i)
              (fun x => Function.invFun (regularUnitBallMap cover (φ (σ j)) i)
                (F j (O.include i x))))) (iteratedFDeriv ℝ m id) atTop B) ∧
      ∀ j, ∀ᶠ k in atTop, j ≤ k ∧
        regularComponent (g (φ (σ k))) (p (φ (σ k))) (4 * δ j) ⊆ F k '' E j := by
  classical
  let U : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun _ => ball 0 1
  let hU : ∀ i, IsOpen (U i) := fun _ => isOpen_ball
  let : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
    fun i => (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, LocallyCompactSpace (Piece U i) := fun i => (hU i).locallyCompactSpace
  let : ∀ i, LocallyConnectedSpace (Piece U i) := fun i => (hU i).locallyConnectedSpace
  let : LocallyConnectedSpace (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isOpen_ball.locallyConnectedSpace
  let e := fun k i => regularUnitBallMap cover (φ k) i
  have hopen := fun k i => regularUnitBallMap_isOpenEmbedding cover hρ hρR (φ k) i
  have hsmooth := fun k i => regularUnitBallMap_isLocalDiffeomorph cover hρ hρR (φ k) i
  have hp := fun i j x y =>
    (hD i j).tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x, y))
  let O := ChartDistance.overlapSystem hp L he c hc hlower hopen (fun k => hconn (φ k))
  have hO := ChartDistance.overlapSystem_smooth U hU hp L he c hc hlower
    hopen (fun k => hconn (φ k)) hsmooth hbound
  have hclosed := ChartDistance.overlapSystem_closed hp L he c hc hlower
    hopen (fun k => hconn (φ k))
  let := quotientChartedSpace U hU O
  have hrel : ∀ i j x y, O.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ D i j (x, y) = 0 :=
    fun i j x y => (ChartDistance.zero_iff_transition hp c hc hlower).symm
  let : PreconnectedSpace (Quotient O.setoid) :=
    regularChartQuotient_preconnected cover hρ hρR hstep hφ hD O hrel L he
  let : Nonempty (Quotient O.setoid) := ⟨O.include 0 ⟨0, by simp⟩⟩
  let : ConnectedSpace (Quotient O.setoid) := ⟨⟨O.include 0 ⟨0, by simp⟩⟩⟩
  let : T2Space (Quotient O.setoid) := O.quotient_t2Space hclosed
  let : LocallyCompactSpace (Quotient O.setoid) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) _
  let : LocallyConnectedSpace (Quotient O.setoid) :=
    ChartDistance.quotient_locallyConnected_of_charts O
  let : SecondCountableTopology (Quotient O.setoid) := O.quotient_secondCountableTopology
  let C : Set (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {x | x.val ∈ closedBall 0 (3 / 4)}
  have hC : IsCompact C := by
    apply isOpen_ball.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
      (isCompact_closedBall 0 (3 / 4))
    intro x hx
    exact ⟨⟨x, closedBall_subset_ball (by norm_num) hx⟩, rfl⟩
  let K : ℕ → Set (Quotient O.setoid) := fun j =>
    ⋃ l : Fin (N j + 1), O.include (Nat.pair j l) '' C
  have hK (j : ℕ) : IsCompact (K j) := isCompact_iUnion fun l : Fin (N j + 1) =>
    hC.image (O.include_isOpenEmbedding (Nat.pair j l)).continuous
  obtain ⟨E, hE, hEc, hEp, hEK, hEstep, hEcover, hKE⟩ :=
    exists_connected_open_exhaustion_capturing_compacts
      (O.include 0 ⟨0, by simp⟩) K hK
  have hEmono : Monotone E := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hEstep j)
  obtain ⟨σ, hσ, V, hV, F, hF, happrox, hjet⟩ :=
    ChartDistance.exists_pointed_source_embeddings_on_compact_sequence U hU hD L he
      c hc hlower hopen (fun k => hconn (φ k)) hsmooth hbound
      (i₀ := 0) ⟨0, by
        change (0 : EuclideanSpace ℝ (Fin n)) ∈ ball 0 1
        exact mem_ball_self zero_lt_one⟩ (fun j => closure (E j)) hEK
  have hFE (j : ℕ) : Topology.IsOpenEmbedding (fun x : E j => F j x) ∧
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F j) (E j) ∧
      F j (O.include 0 ⟨0, by simp⟩) = p (φ (σ j)) := by
    have hEV : E j ⊆ V j := subset_closure.trans
      (subset_union_left.trans (hV j).2.2)
    refine ⟨(hF j).1.comp (.inclusion hEV ((hE j).preimage continuous_subtype_val)),
      (fun x => (hF j).2.1 ⟨x, hEV x.property⟩), ?_⟩
    simpa only [regularUnitBallMap_zero] using (hF j).2.2
  refine ⟨inferInstance, E, hE, hEc, hEp, hEK, hEstep, hEcover,
    σ, hσ, F, hFE, happrox, hjet, ?_⟩
  intro j
  have hcore (l : Fin (N j + 1)) : ∀ᶠ k in atTop,
      regularUnitBallMap cover (φ (σ k)) (Nat.pair j l) ''
        {x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
          x.val ∈ closedBall 0 (1 / 4)} ⊆ F k '' E j := by
    apply eventually_source_core_subset_exhaustion_image (i := Nat.pair j l)
      O hO hE hEmono hEcover F
      (fun k => (hFE k).2.1) (fun k => e (σ k) (Nat.pair j l))
      (fun k => he (σ k) (Nat.pair j l)) (hc (Nat.pair j l))
      (fun k => hlower (σ k) (Nat.pair j l))
      (fun k => hopen (σ k) (Nat.pair j l)) (fun k => hconn (φ (σ k)))
      (fun k => hsmooth (σ k) (Nat.pair j l))
      (happrox (Nat.pair j l)) (hjet (Nat.pair j l)) j
    rintro _ ⟨x, hx, rfl⟩
    have hxhalf : x.val ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := hx
    have hxC : x ∈ C := by
      change x.val ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (3 / 4)
      exact closedBall_subset_closedBall (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hxhalf
    apply hKE j
    exact mem_iUnion.mpr ⟨l, x, hxC, rfl⟩
  have hall := Finset.univ.eventually_all.mpr fun l (_ : l ∈ Finset.univ) => hcore l
  filter_upwards [hall, eventually_ge_atTop j] with k hk hjk
  refine ⟨hjk, ?_⟩
  have hidx : j ≤ φ (σ k) := hjk.trans ((hσ.id_le k).trans (hφ.id_le (σ k)))
  intro y hy
  obtain ⟨l, x, hx, hxy⟩ := mem_iUnion.mp
    ((cover (φ (σ k)) j hidx).unitBallMap_cover (hρ j) hy)
  apply hk l (Finset.mem_univ _)
  refine ⟨x, mem_closedBall_zero_iff.mpr hx, ?_⟩
  rw [regularUnitBallMap_pair cover (φ (σ k)) j hidx l]
  exact hxy

end PoincareConjecture.M28
