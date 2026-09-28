import PoincareConjecture.Proofs.M76.Rigidity.OriginalFillingCutSide
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCollarStrip










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem ball_subset_collar_core (P : OriginalDiskProduct e R j)
    (hfront : frontier P.cutCarrier = (frontier R \ P.openStrip) ∪ P.endDisks)
    (sph : ChartwisePLSphere e (frontier P.cutCarrier))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier P.cutCarrier) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (L.space ×ˢ I) P.cutCarrier)
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {Db : Set X}
    (b : ChartwisePLBall e Db (c '' (L.space ×ˢ {ε}))) (hDbR : Db ⊆ R)
    (hlevelInt : c '' (L.space ×ˢ {ε}) ⊆ interior P.cutCarrier) :
    Db ⊆ P.cutCarrier \ (c '' (L.space ×ˢ Ico 0 ε)) := by
  have hinj : InjOn c (L.space ×ˢ I) := by
    intro z hz w hw heq
    have h : (⟨z, hz⟩ : (L.space ×ˢ I : Set (E × ℝ))) = ⟨w, hw⟩ := hi.injective heq
    exact congrArg Subtype.val h
  obtain ⟨_, _, _, _, hlevel, hBU⟩ := compact_collar_strip_geometry
    (L.isCompact_space_of_finite hL) HB c hc.continuousOn hinj hinside hbase hε hε1
  have hLconn : IsConnected L.space := isConnected_iff_connectedSpace.mpr
    (HB.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp sph.isConnected))
  have hUconn : IsConnected (c '' (L.space ×ˢ Ico 0 ε)) := by
    apply (hLconn.prod (isConnected_Ico hε)).image c
    apply hc.continuousOn.mono
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.le.trans hε1⟩
  have havoid : Disjoint (c '' (L.space ×ˢ Ico 0 ε)) (frontier Db) := by
    rw [b.frontier_eq, ← hlevel]
    exact disjoint_left.mpr (fun _ hxU hx => hx.2 hxU)
  have hDbK := P.ball_subset_cut b hDbR hlevelInt
  have hDbInt : Db ⊆ interior R :=
    b.subset_interior hDbR (hlevelInt.trans (interior_mono (show P.cutCarrier ⊆ R from
      sdiff_subset)))
  obtain ⟨x, hxcap, hxR⟩ := P.exists_old_frontier_witnesses.2
  have hxK : x ∈ frontier P.cutCarrier := by
    rw [hfront]
    exact Or.inr hxcap
  have hxU := hBU hxK
  have hxB : x ∉ Db := fun h => hxR.2 (hDbInt h)
  intro y hyB
  refine ⟨hDbK hyB, ?_⟩
  intro hyU
  exact hxB ((hUconn.isPreconnected.mem_iff_of_disjoint_frontier havoid hxU hyU).mpr hyB)

end PoincareConjecture.M76.OriginalDiskProduct
