import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.AtNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.Separation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

theorem isOpen_tail (P : OpenCylinderModel U) (hU : IsOpen U)
    (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : IsOpen (P.tail side a) := by
  have hcont := P.inverse_smooth.continuousOn.snd
  cases side
  · have heq : P.tail false a = U ∩ (fun x => (P.inverse x).2) ⁻¹' Iio a := by
      ext x
      exact P.mem_tail_iff false ha
    rw [heq]
    exact hcont.isOpen_inter_preimage hU isOpen_Iio
  · have heq : P.tail true a = U ∩ (fun x => (P.inverse x).2) ⁻¹' Ioi a := by
      ext x
      exact P.mem_tail_iff true ha
    rw [heq]
    exact hcont.isOpen_inter_preimage hU isOpen_Ioi

theorem frontier_closedTail_subset_axialSphere (P : OpenCylinderModel U)
    (hU : IsOpen U) (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hclosed : IsClosed (P.closedTail side a)) :
    frontier (P.closedTail side a) ⊆ P.coordinate '' (univ ×ˢ ({a} : Set ℝ)) := by
  intro x hx
  have hxS : x ∈ P.closedTail side a := hclosed.closure_eq ▸ hx.1
  have hxU := ((P.mem_closedTail_iff side ha).mp hxS).1
  have hnot : x ∉ P.tail side a := by
    intro hxtail
    exact hx.2 (interior_mono (P.tail_subset_closedTail side ha)
      ((P.isOpen_tail hU side ha).interior_eq.symm ▸ hxtail))
  have heq : (P.inverse x).2 = a := by
    have hle := ((P.mem_closedTail_iff side ha).mp hxS).2
    have hstrict := P.mem_tail_iff side ha (x := x)
    cases side
    · exact le_antisymm hle (le_of_not_gt (fun h => hnot (hstrict.mpr ⟨hxU, h⟩)))
    · exact le_antisymm (le_of_not_gt (fun h => hnot (hstrict.mpr ⟨hxU, h⟩))) hle
  exact ⟨P.inverse x, ⟨mem_univ _, heq⟩, P.right_inverse hxU⟩

end PoincareConjecture.OpenCylinderModel

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {U : Set M}

theorem isSeparating_of_contained_in_proper_cylinder (N : EpsilonNeck g)
    (P : OpenCylinderModel U) (hU : IsOpen U) (side : Bool)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hclosed : IsClosed (P.closedTail side a)) (hNU : N.carrier ⊆ U) :
    N.IsSeparating := by
  have hSU := N.central_sphere_subset.trans hNU
  obtain ⟨δ, hδ, hlow, hhigh, _, _⟩ :=
    P.exists_tails_disjoint_of_isCompact N.isCompact_central_sphere hSU
  have hδone : δ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.1, hδ.2.trans (by norm_num)⟩
  have hδcomp : 1 - δ ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hδ.1, hδ.2]
  let c : ℝ := if side then δ else 1 - δ
  have hc : c ∈ Ioo (0 : ℝ) 1 := by
    cases side
    · exact hδcomp
    · exact hδone
  apply N.isSeparating_of_closed_cylinder_tail P hU side hc
    (P.isClosed_closedTail_of_isClosed_closedTail side ha hc hclosed) hNU
  intro x hx
  apply (P.mem_closedTail_iff side hc).mpr
  refine ⟨hSU hx, ?_⟩
  cases side
  · exact le_of_not_gt (fun h => disjoint_left.mp hhigh
      ((P.mem_tail_iff true hδcomp).mpr ⟨hSU hx, h⟩) hx)
  · exact le_of_not_gt (fun h => disjoint_left.mp hlow
      ((P.mem_tail_iff false hδone).mpr ⟨hSU hx, h⟩) hx)

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem exists_closed_cylinder_half_at_neck (e : TerminalEnd K)
    {X : Set (E.extended.slice T).carrier}
    (tube : EpsilonTubeCertificate (E.extended.metric T) X)
    (hX : IsClosed X) (hfront : IsCompact (frontier X))
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (N : EpsilonNeck (E.extended.metric T))
    (hepsilon : N.epsilon ≤ 1 / 200) (hNU : N.carrier ⊆ tube.carrier) :
    ∃ (P : OpenCylinderModel tube.carrier) (side : Bool),
      P.middleSphere = N.central_sphere ∧
      IsClosed (P.closedTail side (1 / 2)) ∧
      ∃ k : ℕ, Subtype.val '' e.tail k ⊆ P.closedTail side (1 / 2) := by
  obtain ⟨side, a, k, ha, _, _, hclosed, _, hcarry⟩ :=
    e.exists_proper_closed_tube_tail hX hfront tube n htail
  have hsep := N.isSeparating_of_contained_in_proper_cylinder
    tube.cylinder tube.carrier_open side ha hclosed hNU
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
    exact tube.chain.openCylinderModel_at_neck_of_epsilon_le N
      tube.epsilon_le_threshold hepsilon (hUeq ▸ hNU) hsep
  obtain ⟨P, hPmiddle⟩ := hP
  obtain ⟨newSide, hPclosed, b, hb, hPcapture⟩ :=
    tube.cylinder.exists_closedHalf_of_closedTail P side ha hclosed
  obtain ⟨l, _, hl⟩ := hdir b hb
  exact ⟨P, newSide, hPmiddle, hPclosed, l, (hl l le_rfl).trans hPcapture⟩

end PoincareConjecture.TerminalEnd
