import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Cuts.MarkedFrontier
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCutDomain
import PoincareConjecture.Proofs.M76.Rigidity.OriginalInwardSphere
import PoincareConjecture.Proofs.M76.Rigidity.OriginalFillingCore
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarAttachment










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1



theorem nonempty_cut_ball_of_marked_cylinder
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j) (hI : IsPLIrreducible e N) (hN : IsCompact N)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    (q : V2 × ℝ → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (hq : PolyhedralPLInCharts e q (Q ×ˢ Icc l u))
    (hqi : InjOn q (Q ×ˢ Icc l u))
    (himage : q '' (Q ×ˢ Icc l u) = frontier N \ P.openStrip) :
    Nonempty (ChartwisePLBall e P.cutCarrier (frontier P.cutCarrier)) := by
  obtain ⟨_, _, _, _, _, _, ⟨sph⟩⟩ :=
    P.exists_marked_cut_frontier_sphere hI.1 hN hopen q hlu hlower hupper hq hqi himage
  obtain ⟨hK, _, hfront, _, _, hne⟩ := P.cut_geometry hN hopen
  have heK := P.plDomain_cut hN hI.1 hopen
  obtain ⟨s, K, HB, c, hKfin, hc, hi, hinside, hbase, hproper,
      delta, hdelta, hdsmall, _, hopenC, hlevel, hlevelInt, _⟩ :=
    exists_original_inward_sphere hK heK hne sph isOpen_univ (subset_univ _)
  have hKN : P.cutCarrier ⊆ N := sdiff_subset
  obtain ⟨Db, hDbN, ⟨b⟩⟩ := hI.2 _ (hlevelInt.trans (interior_mono hKN)) hlevel
  obtain ⟨_, ⟨bcore⟩⟩ := P.ball_eq_collar_core hK hfront sph K hKfin HB c hc hi
    hinside hbase hproper hdelta hdsmall hopenC b hDbN hlevelInt
  exact ChartwisePLBall.attach_collar heK K hKfin HB c hc hi hinside hbase hproper
    (half_pos hdelta) (by linarith) bcore

end PoincareConjecture.M76.OriginalDiskProduct
