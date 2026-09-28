import PoincareConjecture.Proofs.M32.Mathlib.ComponentFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

theorem exists_neck_annulus_points_not_joined_of_no_filling
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (hN : N.IsSeparating)
    {U : Set M}
    (hfill : ∀ K₀ : Set M, K₀ ⊆ U → (interior K₀).Nonempty →
      frontier K₀ ⊆ N.central_sphere → ¬ IsCompact K₀)
    {R : ℝ} (hR : 2 * Real.pi + 3 < R)
    (hcompact : IsCompact (closure (g.ball N.center (2 * R * N.scale))))
    (hinside : closure (g.ball N.center (2 * R * N.scale)) ⊆ U) :
    ∃ yNeg yPos : M,
      yNeg ∈ g.ball N.center (2 * R * N.scale) \ g.ball N.center (R * N.scale) ∧
      yPos ∈ g.ball N.center (2 * R * N.scale) \ g.ball N.center (R * N.scale) ∧
      ¬ JoinedIn N.central_sphereᶜ yNeg yPos := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hcontinuous : Continuous (fun y => g.edist N.center y) :=
    continuous_const.edist continuous_id
  have hRpos : 0 < R := by linarith [Real.pi_pos]
  have hRs : 0 < R * N.scale := mul_pos hRpos N.scale_pos
  have hwide : (1 : ℝ) < N.epsilon⁻¹ :=
    (one_lt_inv₀ N.epsilon_pos).mpr (N.epsilon_lt_half.trans (by norm_num))
  let q := (N.coordinate_inverse N.center).1
  have hpoint (a : ℝ) (ha : |a| = 1) :
      N.coordinate_map (q, a) ∈ N.carrier ∧
        (N.coordinate_inverse (N.coordinate_map (q, a))).2 = a ∧
        g.edist N.center (N.coordinate_map (q, a)) ≤
          ENNReal.ofReal ((2 * Real.pi + 2) * N.scale) := by
    have habound := abs_le.mp ha.le
    have hdom : (q, a) ∈ N.cylinderDomain :=
      ⟨mem_univ _, by constructor <;> linarith [habound.1, habound.2]⟩
    have hmem := N.coordinate_map_mem hdom
    have hinv := N.coordinate_inverse_coordinate_map hdom
    refine ⟨hmem, congrArg Prod.snd hinv, ?_⟩
    have hd := N.edist_central_sphere_le_of_mem_carrier hmem N.center_on_central_sphere
    have hcomm : g.edist N.center (N.coordinate_map (q, a)) =
        g.edist (N.coordinate_map (q, a)) N.center := Manifold.riemannianEDist_comm
    rw [hcomm]
    simpa only [hinv, ha, mul_one] using hd
  let vNeg := N.coordinate_map (q, (-1 : ℝ))
  let vPos := N.coordinate_map (q, (1 : ℝ))
  have hm := hpoint (-1) (by norm_num)
  have hp := hpoint 1 (by norm_num)
  have hmregion : vNeg ∈ N.region (-N.epsilon⁻¹) 0 := by
    refine ⟨hm.1, ?_⟩
    rw [hm.2.1]
    constructor <;> linarith
  have hpregion : vPos ∈ N.region 0 N.epsilon⁻¹ := by
    refine ⟨hp.1, ?_⟩
    rw [hp.2.1]
    exact ⟨zero_lt_one, hwide⟩
  have hmsphere : vNeg ∉ N.central_sphere := fun h =>
    Set.disjoint_left.mp
      (N.central_sphere_disjoint_region (-N.epsilon⁻¹) 0 (Or.inl le_rfl)) h hmregion
  have hpsphere : vPos ∉ N.central_sphere := fun h =>
    Set.disjoint_left.mp
      (N.central_sphere_disjoint_region 0 N.epsilon⁻¹ (Or.inr le_rfl)) h hpregion
  have hchoose (v : M) (hv : v ∉ N.central_sphere)
      (hd : g.edist N.center v ≤ ENNReal.ofReal ((2 * Real.pi + 2) * N.scale)) :
      ∃ y ∈ connectedComponentIn N.central_sphereᶜ v,
        y ∈ g.ball N.center (2 * R * N.scale) \ g.ball N.center (R * N.scale) := by
    obtain ⟨z, hz, hzout⟩ := exists_connectedComponentIn_mem_not_mem_of_no_filling
      N.isClosed_central_sphere hfill hcompact hinside hv
    have hfar : ENNReal.ofReal (2 * R * N.scale) ≤ g.edist N.center z :=
      le_of_not_gt (fun h => hzout (subset_closure h))
    have hmargin : (2 * Real.pi + 2) * N.scale < R * N.scale :=
      mul_lt_mul_of_pos_right (by linarith) N.scale_pos
    have hlo : g.edist N.center v ≤ ENNReal.ofReal (3 * R * N.scale / 2) :=
      hd.trans (ENNReal.ofReal_le_ofReal (hmargin.le.trans (by nlinarith [hRs])))
    have hhi : ENNReal.ofReal (3 * R * N.scale / 2) ≤ g.edist N.center z :=
      (ENNReal.ofReal_le_ofReal (by nlinarith [hRs])).trans hfar
    obtain ⟨y, hy, hvalue⟩ := isPreconnected_connectedComponentIn.intermediate_value
      (mem_connectedComponentIn hv) hz hcontinuous.continuousOn ⟨hlo, hhi⟩
    dsimp only at hvalue
    refine ⟨y, hy, ?_⟩
    change g.edist N.center y < ENNReal.ofReal (2 * R * N.scale) ∧
      ¬ g.edist N.center y < ENNReal.ofReal (R * N.scale)
    rw [hvalue]
    constructor
    · exact (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos (mul_pos (by norm_num) hRpos) N.scale_pos)).mpr
        (by nlinarith [hRs])
    · exact not_lt_of_ge (ENNReal.ofReal_le_ofReal (by nlinarith [hRs]))
  obtain ⟨yNeg, hym, hymannulus⟩ := hchoose vNeg hmsphere hm.2.2
  obtain ⟨yPos, hyp, hypannulus⟩ := hchoose vPos hpsphere hp.2.2
  refine ⟨yNeg, yPos, hymannulus, hypannulus, ?_⟩
  rintro ⟨gamma, hgamma⟩
  let CNeg := connectedComponentIn N.central_sphereᶜ vNeg
  let CPos := connectedComponentIn N.central_sphereᶜ vPos
  let W := (CNeg ∪ range gamma) ∪ CPos
  have hW : IsPreconnected W := by
    have hCNeg : IsPreconnected CNeg := isPreconnected_connectedComponentIn
    have hCPos : IsPreconnected CPos := isPreconnected_connectedComponentIn
    have hleft : IsPreconnected (CNeg ∪ range gamma) :=
      hCNeg.union' ⟨yNeg, hym, ⟨0, gamma.source⟩⟩ (isPreconnected_range gamma.continuous)
    exact hleft.union' ⟨yPos, Or.inr ⟨1, gamma.target⟩, hyp⟩ hCPos
  have hvmW : vNeg ∈ W := Or.inl (Or.inl (mem_connectedComponentIn hmsphere))
  have hvpW : vPos ∈ W := Or.inr (mem_connectedComponentIn hpsphere)
  have hcomponent : W ⊆ connectedComponent N.center := by
    rw [connectedComponent_eq (N.carrier_subset_connectedComponent hm.1)]
    exact hW.subset_connectedComponent hvmW
  have havoid : Disjoint W N.central_sphere := by
    apply Set.disjoint_left.mpr
    rintro y ((hy | ⟨t, rfl⟩) | hy) hyS
    · exact connectedComponentIn_subset N.central_sphereᶜ vNeg hy hyS
    · exact hgamma t hyS
    · exact connectedComponentIn_subset N.central_sphereᶜ vPos hy hyS
  exact N.not_meets_both_halves_of_isSeparating hN hW hcomponent havoid
    ⟨⟨vNeg, hvmW, hmregion⟩, ⟨vPos, hvpW, hpregion⟩⟩

end PoincareConjecture.M32
