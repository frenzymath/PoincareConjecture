import PoincareConjecture.Proofs.M47.LimitCanonicalAncientNeckFamily
import PoincareConjecture.Proofs.M47.LimitCanonicalFamilyComparison
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalNeck
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M47.BlowupControlsSequence
import PoincareConjecture.Proofs.M12.GeneralizedCylinderRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

private theorem physical_control_of_history_family
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {D : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 D.carrier} (N : EpsilonNeck g) (hNs : N.scale = 1)
    {origin Q C : ℝ}
    (raw : GeneralizedFlowCylinder H.generalized D origin Q (Ioc (-1 : ℝ) 0) N.carrier)
    (q : H.generalized.point) (hq : q.1 ∈ H.generalized.interval)
    (hbase : raw.pointMap 0 (by constructor <;> norm_num) N.center = q)
    (hQ : Q = H.generalized.scalar q)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback raw N.coordinate_map)) :
    SurgeryCanonicalControl F q.1 (H.history.forward q.1 hq q.2) N.epsilon C := by
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hc : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have htime (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
      origin + s / Q ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff _).mp ⟨raw.forward s hs N.center⟩
  obtain ⟨e, hmap, hmetric⟩ := H.cylinders_to_surgery D origin Q
    (Ioc (-1 : ℝ) 0) N.carrier ordConnected_Ioc N.carrier_open htime raw
  have hphysical : (F.connection (origin + 0 / Q)).scalarCurvature
      (e.forward 0 hzero N.center) = Q := by
    rw [hmap 0 hzero N.center hc, H.scalar_pullback]
    exact (congrArg H.generalized.scalar hbase).trans hQ.symm
  have hphysicalFamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e N.coordinate_map) := by
    apply hfamily.congr_cylinder
    intro s hs z hz v w
    simp only [generalizedCylinderPullback, surgeryCylinderPullback, dif_pos hs]
    exact (hmetric s hs (N.coordinate_map z)
      (N.coordinate_map_mem_of_axial_mem hz)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w)).symm
  obtain ⟨S, hSc⟩ := limitCanonical_exists_physical_neck N hNs e hphysical hphysicalFamily
  have hcanon : SurgeryCanonicalControl F (origin + 0 / Q)
      (e.forward 0 hzero N.center) N.epsilon C := SurgeryCanonicalControl.neck S hSc
  have hpoint := limitCanonicalPhysicalChart_point_identity raw N.carrier_open H.history
    0 hzero (htime 0 hzero) N.center q hq hbase
  have hchart : limitCanonicalPhysicalChart raw N.carrier_open H.history
      0 hzero (htime 0 hzero) N.center = e.forward 0 hzero N.center :=
    (hmap 0 hzero N.center hc).symm
  rw [hchart] at hpoint
  exact (congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
    SurgeryCanonicalControl F p.1 p.2 N.epsilon C) hpoint).mp hcanon

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime
    basePoint hPositive hDiverges) (blowupBackwardInterval ⊤))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
private local instance : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
private local instance : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : SecondCountableTopology G.limit.carrier.carrier :=
  G.limit.carrier.secondCountable
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace

theorem limitCanonical_eventually_neck_control
    (P : M47Predecessors.{u}) {kappa epsilon C : ℝ}
    (A : M30AncientKappaIdentification G.limit kappa)
    (N : StrongEvolvingNeck A.certificate.solution 0 epsilon)
    (hcenter : N.center = G.limit.base) :
    ∀ᶠ k in atTop,
      SurgeryCanonicalControl (F (G.subsequence k)) (baseTime (G.subsequence k))
        ((history (G.subsequence k)).history.forward (baseTime (G.subsequence k))
          (hbaseTime (G.subsequence k)) (basePoint (G.subsequence k))) epsilon C := by
  obtain ⟨N0, hNe, hNc, _hND, hNs, K, hK, hNK, hfamily⟩ :=
    limitCanonical_exists_ancient_neck_family G.limit A N hcenter
  have hJI : Icc (-1 : ℝ) 0 ⊆ blowupBackwardInterval ⊤ := by
    rw [A.domain_eq]
    exact fun _ hs => hs.2
  filter_upwards [limitCanonical_eventually_neck_family_comparison G P hJI
    N0 hK hNK hfamily] with k hk
  have hunit : Ioc (-1 : ℝ) 0 ⊆ Icc (-G.exhaustion.time k) 0 :=
    Ioc_subset_Icc_self.trans hk.1
  have hspace : N0.carrier ⊆ G.exhaustion.space k := hNK.trans hk.2.1
  let raw : GeneralizedFlowCylinder (history (G.subsequence k)).generalized
      G.limit.sliceCarrier (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
      (Ioc (-1 : ℝ) 0) N0.carrier := (G.embedding k).restrict hunit hspace
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hbase : raw.pointMap 0 hzero N0.center = (V).base (G.subsequence k) := by
    change (G.embedding k).pointMap 0 (hunit hzero) N0.center = (V).base (G.subsequence k)
    rw [hNc]
    exact G.base_preserving k (hunit hzero)
  have hrawFamily : RoundCylinderFamilyClose N0.epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback raw N0.coordinate_map) := by
    apply hk.2.2.congr_cylinder
    intro s hs z _hz v w
    simp only [generalizedCylinderPullback,
      dif_pos hs, dif_pos (hunit hs)]
    rfl
  rw [← hNe]
  exact physical_control_of_history_family (history (G.subsequence k))
    (D := G.limit.sliceCarrier) (g := G.limit.flow.metric 0) N0 hNs
    (origin := baseTime (G.subsequence k)) (Q := (V).scale (G.subsequence k)) raw
    ((V).base (G.subsequence k)) (hbaseTime (G.subsequence k)) hbase rfl hrawFamily

end PoincareConjecture.M47
