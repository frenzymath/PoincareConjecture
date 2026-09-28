import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.ClosedEnd
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeEnds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Cylinder.NeckNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Horn.Tube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Spatial


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}



theorem exists_strongHorn_at_neck_of_epsilon_le (e : TerminalEnd K)
    {X : Set (E.extended.slice T).carrier}
    (tube : EpsilonTubeCertificate (E.extended.metric T) X)
    (hX : IsClosed X) (hfront : IsCompact (frontier X))
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (hepsilon : epsilon ≤ 1 / 200) (N : TerminalStrongNeck E epsilon)
    (hNU : N.carrier ⊆ tube.carrier)
    (hsep : (N.spatialNeck (hepsilon.trans_lt (by norm_num))).IsSeparating)
    (hstrong : ∀ x ∈ tube.carrier, ∃ P : TerminalStrongNeck E epsilon, P.center = x) :
    ∃ horn : StrongHorn E epsilon,
      horn.boundary_sphere = N.central_sphere ∧ horn.carrier ⊆ tube.carrier ∧
      ∃ k : ℕ, Subtype.val '' e.tail k ⊆ horn.carrier := by
  have hhalfε : epsilon < 1 / 2 := hepsilon.trans_lt (by norm_num)
  obtain ⟨side, a, k, ha, _, _, hclosed, _, hcarry⟩ :=
    e.exists_proper_closed_tube_tail hX hfront tube n htail
  let tube' : EpsilonTubeCertificate (E.extended.metric T) (Subtype.val '' e.tail n) :=
    { tube with contains_X := htail.trans tube.contains_X }
  obtain ⟨side', hdir⟩ := e.exists_tube_direction n tube'
  have hsides : side' = side := by
    obtain ⟨j, _, hj⟩ := hdir a ha
    obtain ⟨x, hx⟩ := (e.tail_image_connected (max j k)).nonempty
    have hfirst := ((tube.cylinder.mem_tail_iff side' ha).mp
      (hj _ (le_max_left _ _) hx)).2
    have hsecond := ((tube.cylinder.mem_tail_iff side ha).mp
      (hcarry _ (le_max_right _ _) hx)).2
    cases side' <;> cases side <;> first | rfl | exact False.elim (lt_asymm hfirst hsecond)
  subst side'
  have hUeq : tube.carrier = (tube.chain.unionOpen : Set (E.extended.slice T).carrier) :=
    tube.carrier_eq_chain_union
  have hP : ∃ P : OpenCylinderModel tube.carrier, P.middleSphere = N.central_sphere := by
    rw [hUeq]
    exact tube.chain.openCylinderModel_at_neck_of_epsilon_le (N.spatialNeck hhalfε)
      tube.epsilon_le_threshold hepsilon (hUeq ▸ hNU) hsep
  obtain ⟨P, hPmiddle⟩ := hP
  obtain ⟨newSide, hPclosed, b, hb, hPcapture⟩ :=
    tube.cylinder.exists_closedHalf_of_closedTail P side ha hclosed
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨r, hr, hsmooth⟩ := P.halfParameterization_smooth_collar newSide hhalf
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
  have hhalfU : P.closedTail newSide (1 / 2) ⊆ tube.carrier :=
    fun _ hx => ((P.mem_closedTail_iff newSide hhalf).mp hx).1
  let horn : StrongHorn E epsilon := {
    carrier := P.closedTail newSide (1 / 2)
    coordinate := P.halfHomeomorph newSide hhalf
    parameterization := P.halfParameterization newSide (1 / 2)
    coordinate_eq := P.halfHomeomorph_eq newSide hhalf
    collar := r
    collar_pos := hr
    parameterization_smooth := hsmooth
    parameterization_regular := P.halfParameterization_regular tube.carrier_open newSide hhalf
    proper := fun L hL => P.halfParameterization_proper newSide hhalf hPclosed hL
    boundary_sphere := N.central_sphere
    boundary_sphere_eq := hPmiddle.symm.trans hboundary.symm
    boundary_neck := ⟨N, rfl⟩
    every_point_neck := fun x hx => hstrong x (hhalfU hx) }
  obtain ⟨l, _, hl⟩ := hdir b hb
  exact ⟨horn, rfl, hhalfU, l, (hl l le_rfl).trans hPcapture⟩

end PoincareConjecture.TerminalEnd
