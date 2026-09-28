import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.RetainedPhaseModels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FiniteComponentExcision

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.FrontierResidualModel

local notation "V3" => (Fin 3 → ℝ)

theorem exists_model_after_closed_excision
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N F D : Set X}
    (M : FrontierResidualModel e N F) (hD : IsClosed D)
    (hfront : Disjoint F (frontier D)) (hnewne : (F \ interior D).Nonempty) :
    ∃ Mnew : FrontierResidualModel e N (F \ interior D),
      Mnew.complexity ≤ M.complexity ∧ Mnew.count ≤ M.count ∧
      ((F ∩ D).Nonempty → Mnew.count < M.count) := by
  classical
  by_cases hmeet : (F ∩ D).Nonempty
  · obtain ⟨J, hcard, _, hnew, _⟩ :=
      Poincare.Topology.exists_finite_component_excision M.components hD
        (fun i => (M.component i).2.1.isPreconnected)
        (fun i => hfront.mono_left (M.component i).2.2.1)
        (fun i x hx => by rw [M.cover]; exact (M.component i).2.2.2 x hx)
        (M.cover.symm ▸ hmeet)
    rw [M.cover] at hnew
    have hJ : J.Nonempty := by
      obtain ⟨x, hx⟩ := hnew.symm ▸ hnewne
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      obtain ⟨hjJ, _⟩ := mem_iUnion.mp hj
      exact ⟨j, hjJ⟩
    obtain ⟨Mnew, hcount, hcomplexity⟩ := M.exists_retained_finset_model J hJ
    have hlt : Mnew.count < M.count := by simpa only [hcount, Fintype.card_fin] using hcard
    exact hnew.symm ▸ ⟨Mnew, hcomplexity, hlt.le, fun _ => hlt⟩
  · have hnew : F \ interior D = F := by
      apply sdiff_eq_left.mpr
      exact Set.disjoint_left.mpr (fun x hx hxD => hmeet ⟨x, hx, interior_subset hxD⟩)
    rw [hnew]
    exact ⟨M, le_rfl, le_rfl, fun h => (hmeet h).elim⟩

end PoincareConjecture.M76.FrontierResidualModel
