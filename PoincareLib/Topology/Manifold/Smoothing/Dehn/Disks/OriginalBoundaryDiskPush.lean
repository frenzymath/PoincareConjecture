import PoincareLib.Topology.Manifold.Smoothing.Dehn.Collars.Mathlib.BoundaryDiskCollarPush
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Collars.ProtectedBoundaryCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.OriginalChartBall
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonWallComplementBall

/-!
# Construct the inward disk push from the actual original PL domain

The boundary disk supplies a real point of the domain. Its actual
halfspace charts give interior density, hence an interior chart
ball. That ball and the compact domain construct the whole original
collar internally, before the exact variable-height disk push.
See Dehn derivation 026, sections 1--5.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- A compact original PL domain and its actual embedded boundary
disk construct a proper embedded PL disk with every original rim
value fixed. The chart ball and whole collar are produced inside
the proof. See Dehn026, sections 1--5. -/
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

end PoincareMT.M76.Dehn
