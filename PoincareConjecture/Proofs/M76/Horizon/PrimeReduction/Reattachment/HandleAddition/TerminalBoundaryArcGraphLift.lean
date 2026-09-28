import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcLift
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.QuotientLiftDifference

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_injective_terminal_graph_lift
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {A qA W : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W ⊆ A) (hW : IsConnected W)
    (hcontact : f '' A ∩ S = f '' W)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    {End Z : Set X} (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup))
    (hFi : Function.Injective F)
    (hFhom : F.Homotopic (q.comp ⟨Subtype.val,continuous_subtype_val⟩))
    (hZE : Z ⊆ End) (hZS : Z ⊆ S ∪ f '' A) :
    ∃ J : C(Z,κ → ℝ), Function.Injective J ∧
      ∀ x : Z, QuotientAddGroup.mk (J x) = F ⟨x,hZE x.property⟩ := by
  obtain ⟨G,hG⟩ := s.exists_lattice_lift_with_attached_disk L hA hf hfi hWA hW hcontact q
  let incS : C(Z,↥(S ∪ f '' A)) := ⟨Set.inclusion hZS,continuous_inclusion _⟩
  let incE : C(Z,End) := ⟨Set.inclusion hZE,continuous_inclusion _⟩
  let first : C(Z,κ → ℝ) := G.comp incS
  obtain ⟨H⟩ := hFhom.symm.comp (ContinuousMap.Homotopic.refl incE)
  have hp := (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    DiscreteTopology.isDiscrete).isCoveringMap
  have hzero (x : Z) : H (0,x) = QuotientAddGroup.mk (first x) := by
    rw [H.apply_zero]
    exact (hG (incS x)).symm
  let lifted := hp.liftHomotopy H.toContinuousMap first hzero
  let J : C(Z,κ → ℝ) := lifted.comp ⟨fun x => (1,x),by fun_prop⟩
  have hJ (x : Z) : QuotientAddGroup.mk (J x) = F ⟨x,hZE x.property⟩ := by
    have hh := congrFun (hp.liftHomotopy_lifts H.toContinuousMap first hzero) (1,x)
    exact hh.trans (H.apply_one x)
  refine ⟨J,?_,hJ⟩
  intro x y hxy
  apply Subtype.ext
  have hh := hFi ((hJ x).symm.trans ((congrArg QuotientAddGroup.mk hxy).trans (hJ y)))
  exact congrArg (fun z : End => (z : X)) hh

theorem exists_normalized_lattice_lift_on_connected_mark
    {Z Y κ : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    [PreconnectedSpace Y] [Nonempty Y] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    (F : C(Z,(κ → ℝ) ⧸ L.toAddSubgroup)) (J : C(Z,κ → ℝ))
    (hJi : Function.Injective J) (hJ : ∀ z, QuotientAddGroup.mk (J z) = F z)
    (c : C(Y,Z)) (v : C(Y,κ → ℝ))
    (hv : ∀ y, QuotientAddGroup.mk (v y) = F (c y)) :
    ∃ K : C(Z,κ → ℝ), Function.Injective K ∧
      (∀ z, QuotientAddGroup.mk (K z) = F z) ∧ ∀ y, K (c y) = v y := by
  classical
  let y0 : Y := Classical.choice inferInstance
  let d := v y0 - J (c y0)
  let K : C(Z,κ → ℝ) := ⟨fun z => J z + d,J.continuous.add continuous_const⟩
  have hd : (QuotientAddGroup.mk d : (κ → ℝ) ⧸ L.toAddSubgroup) = 0 := by
    change (QuotientAddGroup.mk' L.toAddSubgroup) (v y0 - J (c y0)) = 0
    rw [map_sub]
    change QuotientAddGroup.mk (v y0) - QuotientAddGroup.mk (J (c y0)) = 0
    rw [hv,hJ,sub_self]
  refine ⟨K,?_,?_,?_⟩
  · intro x y hh
    exact hJi (add_right_cancel hh)
  · intro z
    change (QuotientAddGroup.mk' L.toAddSubgroup) (J z + d) = _
    rw [map_add]
    change QuotientAddGroup.mk (J z) + QuotientAddGroup.mk d = F z
    rw [hd,add_zero,hJ]
  · intro y
    have hh := quotient_lift_endpoint_difference L (J.comp c) v
      (fun z => (hJ (c z)).trans (hv z).symm) y0 y
    change J (c y) - J (c y0) = v y - v y0 at hh
    change J (c y) + (v y0 - J (c y0)) = v y
    linear_combination hh

end PoincareConjecture.M76
