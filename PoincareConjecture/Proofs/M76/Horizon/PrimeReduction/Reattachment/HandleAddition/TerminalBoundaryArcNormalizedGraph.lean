import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcGraphLift

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1

theorem ChartwisePLSphere.exists_normalized_terminal_graph_lift
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
    {End Z B : Set X} (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup))
    (hFi : Function.Injective F)
    (hFhom : F.Homotopic (q.comp ⟨Subtype.val,continuous_subtype_val⟩))
    (hZE : Z ⊆ End) (hZS : Z ⊆ S ∪ f '' A)
    (H : (CY × unitInterval) ≃ₜ B) (hBE : B ⊆ End)
    (hcore : ∀ y, (H (y,1) : X) ∈ Z)
    (v : C(CY,κ → ℝ)) (hvn : ∀ y, ‖v y‖ = (3/2 : ℝ))
    (hFB : ∀ z, F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1)) :
    ∃ J : C(Z,κ → ℝ), Function.Injective J ∧
      (∀ x : Z, QuotientAddGroup.mk (J x) = F ⟨x,hZE x.property⟩) ∧
      (∀ y, J ⟨H (y,1),hcore y⟩ = (1/2 : ℝ) • v y) ∧
      ∀ y, ‖J ⟨H (y,1),hcore y⟩‖ = (3/4 : ℝ) := by
  let : ConnectedSpace CY := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank];simp) (0 : Fin 2 → ℝ) zero_le_one)
  let : Nonempty CY := (NormedSpace.sphere_nonempty.mpr zero_le_one :
    (sphere (0 : Fin 2 → ℝ) 1).Nonempty).to_subtype
  obtain ⟨J,hJi,hJ⟩ := s.exists_injective_terminal_graph_lift L hA hf hfi hWA hW hcontact
    q F hFi hFhom hZE hZS
  let FZ : C(Z,(κ → ℝ) ⧸ L.toAddSubgroup) :=
    F.comp ⟨Set.inclusion hZE,continuous_inclusion _⟩
  let c : C(CY,Z) := ⟨fun y => ⟨H (y,1),hcore y⟩,
    (continuous_subtype_val.comp (H.continuous.comp
      (continuous_id.prodMk continuous_const))).subtype_mk _⟩
  let vhalf : C(CY,κ → ℝ) := ⟨fun y => (1/2 : ℝ) • v y,by fun_prop⟩
  have hv (y : CY) : QuotientAddGroup.mk (vhalf y) = FZ (c y) := by
    convert (hFB (y,1)).symm using 1 <;> norm_num [vhalf,FZ,c]
  obtain ⟨K,hKi,hK,hKv⟩ := exists_normalized_lattice_lift_on_connected_mark L FZ J hJi hJ c vhalf hv
  refine ⟨K,hKi,hK,hKv,?_⟩
  intro y
  change ‖K (c y)‖ = _
  rw [hKv]
  change ‖(1/2 : ℝ) • v y‖ = _
  rw [norm_smul,Real.norm_eq_abs,hvn]
  norm_num

end PoincareConjecture.M76
