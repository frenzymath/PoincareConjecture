import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClopenDomainFrontier
import Mathlib.Topology.Connected.PathConnected











set_option autoImplicit false

open Set

namespace Set




theorem exists_compact_connected_carrier
    {X : Type*} [TopologicalSpace X] {P R : Set X}
    [LocallyConnectedSpace P] (hP : IsCompact P) (hne : P.Nonempty)
    (hPR : P ⊆ R) (hR : IsPathConnected R) :
    ∃ T : Set X, IsCompact T ∧ IsConnected T ∧ P ⊆ T ∧ T ⊆ R := by
  classical
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  obtain ⟨x, hxP⟩ := hne
  choose p hp using (fun c : ConnectedComponents P => ConnectedComponents.surjective_coe c)
  let joined (c : ConnectedComponents P) : JoinedIn R x (p c : X) :=
    hR.joinedIn x (hPR hxP) (p c) (hPR (p c).property)
  let gamma (c : ConnectedComponents P) : Path x (p c : X) := (joined c).somePath
  let G (c : ConnectedComponents P) : Set X :=
    connectedComponentIn P (p c : X) ∪ range (gamma c)
  have hGc (c : ConnectedComponents P) : IsCompact (G c) :=
    (isCompact_connectedComponentIn_of_mem hP (p c).property).union
      (isCompact_range (gamma c).continuous)
  have hGconn (c : ConnectedComponents P) : IsConnected (G c) :=
    IsConnected.union
      ⟨(p c : X), mem_connectedComponentIn (p c).property,
        ⟨1, (gamma c).target⟩⟩
      (isConnected_connectedComponentIn_iff.mpr (p c).property)
      (isConnected_range (gamma c).continuous)
  have hxG (c : ConnectedComponents P) : x ∈ G c :=
    Or.inr ⟨0, (gamma c).source⟩
  have hPG : P ⊆ ⋃ c, G c := by
    intro y hy
    let q : P := ⟨y, hy⟩
    let c : ConnectedComponents P := q
    have hcomp : connectedComponent (p c) = connectedComponent q :=
      ConnectedComponents.coe_eq_coe.mp (hp c)
    have hycomp : q ∈ connectedComponent (p c) := by
      rw [hcomp]
      exact mem_connectedComponent
    apply mem_iUnion.mpr
    refine ⟨c, Or.inl ?_⟩
    rw [connectedComponentIn_eq_image (p c).property]
    exact ⟨q, hycomp, rfl⟩
  refine ⟨⋃ c, G c, isCompact_iUnion hGc,
    ⟨⟨x, hPG hxP⟩, isPreconnected_iUnion ⟨x, mem_iInter.mpr hxG⟩
      (fun c => (hGconn c).isPreconnected)⟩, hPG, ?_⟩
  intro y hy
  obtain ⟨c, hc⟩ := mem_iUnion.mp hy
  rcases hc with hc | ⟨t, rfl⟩
  · exact hPR (connectedComponentIn_subset P (p c : X) hc)
  · exact (joined c).somePath_mem t

end Set
