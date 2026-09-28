import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BoundaryDiskCollarPush
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryCollar
import PoincareConjecture.Proofs.M76.Rigidity.OriginalChartBall
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1





theorem exists_original_boundary_disk_push
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (hN : IsCompact N) (he : PLDomain e N)
    (hj : PolyhedralPLInCharts e j D)
    (hjemb : Topology.IsEmbedding (fun x : D => j x))
    (hjB : MapsTo j D (frontier N)) :
    ∃ k : V2 → X, PolyhedralPLInCharts e k D ∧
      Topology.IsEmbedding (fun x : D => k x) ∧ MapsTo k D N ∧
      EqOn k j Q ∧ ∀ x : D, k x ∈ frontier N ↔ (x : V2) ∈ Q := by
  have hNne : N.Nonempty :=
    ⟨j 0, he.closed.frontier_subset (hjB (mem_closedBall_self zero_le_one))⟩
  have hne : (interior N).Nonempty := closure_nonempty_iff.mp
    (he.closure_interior.symm ▸ hNne)
  obtain ⟨B, _, hBN, ⟨b⟩⟩ := he.exists_ball_in_interior hne
  obtain ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproper, _⟩ :=
    exists_protected_small_boundary_collar hN he (hBN.trans interior_subset) b
      isOpen_univ (fun _ _ => mem_univ _)
  exact exists_collar_pushed_boundary_disk he.compatible hj hjemb hjB
    L hL HB c hc hi hinside hbase hproper

end PoincareConjecture.M76.Dehn
