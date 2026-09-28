import PoincareConjecture.Proofs.M56.FiniteTrace
import PoincareConjecture.Proofs.M56.TracePath
import PoincareConjecture.Proofs.M56.GroupInduction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m56FinitePathCover {F : SurgeryFlowData.{u}} {W : RepairedEventChildWitness F}
    (T : ℝ) (hT : T ∈ F.time_domain)
    (paths : (F.slice T).carrier → RepairedComponentPath F T W)
    (cover : ∀ x, x ∈ range ((paths x).component
      ⟨T, F.time_domain_nonnegative hT, le_rfl⟩).inclusion) :
    ∃ n : ℕ, ∃ paths' : Fin n → RepairedComponentPath F T W,
      ∀ x : (F.slice T).carrier, ∃ i : Fin n,
        x ∈ range ((paths' i).component
          ⟨T, F.time_domain_nonnegative hT, le_rfl⟩).inclusion := by
  classical
  let U := fun x => range ((paths x).component
    ⟨T, F.time_domain_nonnegative hT, le_rfl⟩).inclusion
  have hopen (x) : IsOpen (U x) := by
    let C := (paths x).component ⟨T, F.time_domain_nonnegative hT, le_rfl⟩
    exact C.inclusion_openEmbedding.isOpen_range
  obtain ⟨s, hs⟩ := (F.slices_compact T hT).elim_finite_subcover U hopen
    (fun x _ => mem_iUnion.mpr ⟨x, cover x⟩)
  refine ⟨s.card, fun i => paths (s.equivFin.symm i).1, ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  refine ⟨s.equivFin ⟨y, hy⟩, ?_⟩
  change x ∈ U (s.equivFin.symm (s.equivFin ⟨y, hy⟩)).1
  simpa only [Equiv.symm_apply_apply] using hxy

theorem m56FiniteAncestry (G54 : RepairedGroupEffectsTheory.{u})
    {F : SurgeryFlowData.{u}} (W : RepairedEventChildWitness F)
    (hconn : IsConnected (univ : Set (F.slice 0).carrier))
    (hzero : M56PointGroups (F.slice 0))
    (hfinite : ∀ H : ℝ, 0 ≤ H → (F.surgery_times ∩ Icc 0 H).Finite) :
    Nonempty (RepairedFiniteAncestryData F W) := by
  classical
  let C0 := m56SelectedComponent (F.slices_compact 0 F.zero_mem)
    (Classical.choice F.initial_nonempty)
  have hC0 : range C0.inclusion = univ := by
    let : ConnectedSpace (F.slice 0).carrier := connectedSpace_iff_univ.mpr hconn
    dsimp only [C0]
    rw [m56SelectedComponent_range, PreconnectedSpace.connectedComponent_eq_univ]
  let trace := fun T hT x => Classical.choose (m56Trace_exists F T hT x)
  let paths : ∀ (T : ℝ) (_hT : T ∈ F.time_domain) (_x : (F.slice T).carrier),
      RepairedComponentPath F T W := fun T hT x =>
    m56TracePath G54 W (trace T hT x) hT C0 hC0 hconn
      (m56PointGroups_of_witness F W hzero)
  have cover (T : ℝ) (hT : T ∈ F.time_domain) (x : (F.slice T).carrier) :
      x ∈ range ((paths T hT x).component
        ⟨T, F.time_domain_nonnegative hT, le_rfl⟩).inclusion := by
    change x ∈ range (m56TraceComponents (trace T hT x) C0
      ⟨T, F.time_domain_nonnegative hT, le_rfl⟩).inclusion
    rw [m56TraceComponents_range _ _ hC0 hconn]
    exact Classical.choose_spec (m56Trace_exists F T hT x)
  refine ⟨{
    initial_component := C0
    initial_component_cover := hC0
    path_for := paths
    path_for_initial := ?_
    path_for_terminal_cover := cover
    finite_path_cover := fun T hT => m56FinitePathCover T hT (paths T hT) (cover T hT)
    bounded_event_count := hfinite }⟩
  intro T hT x
  exact m56TraceComponents_zero (trace T hT x) C0 (F.time_domain_nonnegative hT)

end PoincareConjecture
