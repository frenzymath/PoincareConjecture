import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Loops.OriginalComponentAlternative











set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

open Classical in
theorem PLDomain.nonspherical_frontier_component_groups
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N B F S : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hNne : N.Nonempty)
    (hB : IsClosed B) (hF : IsClosed F) (hBF : Disjoint B F)
    (hfront : frontier N = B ∪ F) (hS : IsConnected S) (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (hnonsphere : ¬ Nonempty (ChartwisePLSphere e S)) :
    IsPathConnected S ∧ (∀ x : S, Nontrivial (FundamentalGroup S x)) ∧
      ∃ (v : V2 → X) (gamma : C(Q, S)),
        Topology.IsEmbedding gamma ∧ PolyhedralPLInCharts e v Q ∧
        (∀ z : Q, (gamma z : X) = v z) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  obtain ⟨s, phi, K, A, H, g, HB, n, pick, C,
    _, _, hK, hAK, _, _, _, _, _, _, hg, hgPL, _, _, _, _,
    hpure, hcofaces, hlinks, _, _, hcover, _, hcomponents, _⟩ :=
    he.exists_new_frontier_component_models hN hNne hB hF hBF hfront
      (hS.nonempty.mono hSF)
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover.symm ▸ hSF hx)
  have hCS : C j = S := ((hcomponents j).2.2.2.1 x hxj).symm.trans (hcomponent x hx)
  obtain ⟨HC, hHC⟩ := (hcomponents j).2.2.2.2.2
  let HS : (A.edgeComponentComplex (pick j)).space ≃ₜ S :=
    HC.trans (Homeomorph.setCongr hCS)
  have hHS (z) : (HS z : X) = g z := hHC z
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have h : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ :=
      Subtype.ext ((hg ⟨x, hx⟩).symm.trans (hxy.trans (hg ⟨y, hy⟩)))
    exact congrArg Subtype.val (H.symm.injective h)
  obtain hsphere | ⟨m, P, a, d, gamma, _, _, _, _, _, _, _, _,
    hgamma, _, hemb, hd, hnontrivial⟩ :=
    original_frontier_component_sphere_or_essential_rim e K A hK hAK (pick j)
      hpure hcofaces hlinks (Subset.refl S)
      (fun x hx => hS.isPreconnected.connectedComponentIn hx)
      HS (fun z => (g z : X)) hHS hgPL hgi
  · exact (hnonsphere hsphere).elim
  let : PathConnectedSpace (A.edgeComponentComplex (pick j)).space :=
    isPathConnected_iff_pathConnectedSpace.mp (A.edgeComponentComplex_isPathConnected (pick j))
  let : PathConnectedSpace S := HS.surjective.pathConnectedSpace HS.continuous
  have hnontriv : Nontrivial (FundamentalGroup S (gamma Dehn.squareRimBase)) :=
    ⟨⟨_, 1, hnontrivial⟩⟩
  refine ⟨isPathConnected_iff_pathConnectedSpace.mpr inferInstance, ?_,
    fun z => g (d z), gamma, hemb, hd, hgamma, hnontrivial⟩
  intro y
  let : Nontrivial (FundamentalGroup S (gamma Dehn.squareRimBase)) := hnontriv
  exact (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    (gamma Dehn.squareRimBase) y).injective.nontrivial

end PoincareConjecture.M76
