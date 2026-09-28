import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Horn.Tube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.NeckConfinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.NeckNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.HalfNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.TerminalEnd



theorem exists_strongHorn_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (E : GeneralizedFlowExtension F T) (K : TerminalComponentPath E)
        (e : TerminalEnd K) (A : RepairedNeckCapTopologyTheory.{u})
        {epsilon C B : ℝ},
        0 < epsilon → 0 < C → epsilon ≤ ε₀ → epsilon ≤ A.epsilon₀ →
        (∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x) →
        (∀ D : Set ℝ, IsCompact D →
          IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D)) →
        (∀ x : (E.extended.slice T).carrier,
          B < (E.extended.connection T).scalarCurvature x →
            GeneralizedCanonicalControl (F := E.extended) T x epsilon C) →
        ∃ Hn : StrongHorn E epsilon,
          Hn.carrier ⊆ K.component ∧ ∃ n : ℕ, Subtype.val '' e.tail n ⊆ Hn.carrier := by
  obtain ⟨ε₁, hε₁, hsmall, hneck⟩ := exists_strong_neck_tail_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hconfine⟩ := exists_neck_confinement_threshold.{u}
  obtain ⟨ε₃, hε₃, _, hnormalize⟩ :=
    BalancedNeckChain.exists_openCylinderModel_at_neck_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro F T E K e A epsilon C B hepsilon hC hε hA hlower hproper hcanonical
  have hb : epsilon ≤ ε₁ ∧ epsilon ≤ ε₂ ∧ epsilon ≤ ε₃ := by
    simpa only [le_min_iff] using hε
  have hhalfε : epsilon < 1 / 2 := (hb.1.trans hsmall).trans_lt (by norm_num)
  obtain ⟨k, hk⟩ := hneck E K e A hepsilon hC hb.1 hA hlower hproper hcanonical
  obtain ⟨X, tube, htube, side, a, ha, hclosed, hhalf, hdir⟩ :=
    e.exists_tube_closed_half_in_tail A hepsilon hC hA hlower hproper hcanonical k
  have hhalfneck : ∀ x ∈ tube.cylinder.closedTail side a,
      ∃ N : TerminalStrongNeck E epsilon, N.center = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hhalf hx
    exact hk k le_rfl y hy
  obtain ⟨k₁, hk₁⟩ := hdir a ha
  have hcapture : Subtype.val '' e.tail k₁ ⊆ tube.cylinder.closedTail side a :=
    (hk₁ k₁ le_rfl).trans (tube.cylinder.tail_subset_closedTail side ha)
  obtain ⟨n, _, hn⟩ := hconfine E K e hb.2.1 hlower hproper k₁ ∅ isCompact_empty
  obtain ⟨x, hx⟩ := (e.tail_connected (max n k₁)).nonempty
  have hxhalf : (x : (E.extended.slice T).carrier) ∈ tube.cylinder.closedTail side a :=
    hcapture ⟨x, e.nested (le_max_right n k₁) hx, rfl⟩
  obtain ⟨N, hNcenter⟩ := hhalfneck x hxhalf
  have hNhalf : N.carrier ⊆ tube.cylinder.closedTail side a :=
    (hn (max n k₁) (le_max_left _ _) x hx N hNcenter).1.trans hcapture
  have hNU : N.carrier ⊆ tube.carrier := fun y hy =>
    ((tube.cylinder.mem_closedTail_iff side ha).mp (hNhalf hy)).1
  let Ns := N.spatialNeck hhalfε
  have hsep : Ns.IsSeparating := Ns.isSeparating_of_closed_cylinder_tail tube.cylinder
    tube.carrier_open side ha hclosed hNU (N.central_sphere_subset.trans hNhalf)
  have hUeq : tube.carrier = (tube.chain.unionOpen : Set (E.extended.slice T).carrier) :=
    tube.carrier_eq_chain_union
  have hP : ∃ P : OpenCylinderModel tube.carrier, P.middleSphere = N.central_sphere := by
    rw [hUeq]
    exact hnormalize tube.chain Ns (htube.symm ▸ hb.2.2) hb.2.2
      (hUeq ▸ hNU) hsep
  obtain ⟨P, hPmiddle⟩ := hP
  obtain ⟨newSide, hPclosed, hPsub, b, hb, hPcapture⟩ :=
    tube.cylinder.exists_closedHalf_inside_closedTail P side ha hclosed
      (hPmiddle ▸ N.central_sphere_subset.trans hNhalf)
  have hhalfunit : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨r, hr, hsmooth⟩ := P.halfParameterization_smooth_collar newSide hhalfunit
  have hzero (q : UnitTwoSphere) :
      P.halfParameterization newSide (1 / 2) (q, 0) = P.coordinate (q, 1 / 2) := by
    cases newSide <;> simp [OpenCylinderModel.halfParameterization, OpenCylinderModel.halfAxial]
  have hboundary : P.halfParameterization newSide (1 / 2) ''
      (univ ×ˢ ({0} : Set ℝ)) = P.middleSphere := by
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht : t = 0 := ht
      subst t
      exact ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, (hzero q).symm⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht : t = 1 / 2 := ht
      subst t
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, hzero q⟩
  let Hn : StrongHorn E epsilon := {
    carrier := P.closedTail newSide (1 / 2)
    coordinate := P.halfHomeomorph newSide hhalfunit
    parameterization := P.halfParameterization newSide (1 / 2)
    coordinate_eq := P.halfHomeomorph_eq newSide hhalfunit
    collar := r
    collar_pos := hr
    parameterization_smooth := hsmooth
    parameterization_regular := P.halfParameterization_regular tube.carrier_open newSide hhalfunit
    proper := fun L hL => P.halfParameterization_proper newSide hhalfunit hPclosed hL
    boundary_sphere := N.central_sphere
    boundary_sphere_eq := hPmiddle.symm.trans hboundary.symm
    boundary_neck := ⟨N, rfl⟩
    every_point_neck := fun y hy => hhalfneck y (hPsub hy) }
  obtain ⟨n, hn⟩ := hdir b hb
  refine ⟨Hn, ?_, n, (hn n le_rfl).trans hPcapture⟩
  intro y hy
  obtain ⟨z, _, rfl⟩ := hhalf (hPsub hy)
  exact z.property

end PoincareConjecture.TerminalEnd
