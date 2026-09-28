import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CutGraphHomologyBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CutInclusionHomology









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits HomologicalComplex AlgebraicTopology

universe u
namespace PoincareConjecture.M76.CutGraph
open ModTwoMayerVietoris

theorem cut_graph_homology_comp_zero
    {X I : Type u} [TopologicalSpace X] [Fintype I] [DecidableEq I]
    (R Q : Set X) (hQR : Q ⊆ R) [Fintype (ConnectedComponents Q)]
    [DecidableEq (ConnectedComponents Q)]
    (D : ConnectedComponents Q → Set X)
    (hactual : ∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x)
    (ends : I → Bool → ConnectedComponents Q) (q : C(R, carrier ends))
    (hq : ∀ v (x : R), (x : X) ∈ D v → (q x : Ambient (ConnectedComponents Q) I) = vertex v)
    (n : ℕ) (hn : n ≠ 0) :
    homologyMapOf (⟨Set.inclusion hQR, continuous_inclusion _⟩ : C(Q, R)) n ≫
      homologyMapOf q n = 0 := by
  let j : C(Q, R) := ⟨Set.inclusion hQR, continuous_inclusion _⟩
  let vmap : ConnectedComponents Q → carrier ends := fun v => ⟨vertex v, vertex_mem_carrier ends v⟩
  have hv (x : Q) : vmap (ConnectedComponents.mk x) = q (j x) := by
    apply Subtype.ext
    apply Eq.symm
    apply hq
    rw [hactual x]
    exact mem_connectedComponentIn x.property
  have hc : Continuous vmap := by
    apply ConnectedComponents.isQuotientMap_coe.continuous_iff.mpr
    have he : vmap ∘ ConnectedComponents.mk = q ∘ j := funext hv
    rw [he]
    exact q.continuous.comp j.continuous
  let v : C(ConnectedComponents Q, carrier ends) := ⟨vmap, hc⟩
  let p : C(Q, ConnectedComponents Q) := ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  have hf : q.comp j = v.comp p := ContinuousMap.ext (fun x => (hv x).symm)
  have hz : IsZero (homology (ConnectedComponents Q) n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} (ZMod 2)) n coefficient (TopCat.of (ConnectedComponents Q)) hn
  have he : homologyMapOf j n ≫ homologyMapOf q n =
      homologyMapOf p n ≫ homologyMapOf v n := by
    calc
      _ = homologyMapOf (q.comp j) n := by
        unfold homologyMapOf chainMap
        rw [← homologyMap_comp, ← CategoryTheory.Functor.map_comp]
        rfl
      _ = homologyMapOf (v.comp p) n := congrArg (fun f => homologyMapOf f n) hf
      _ = _ := by
        unfold homologyMapOf chainMap
        rw [← homologyMap_comp, ← CategoryTheory.Functor.map_comp]
        rfl
  change homologyMapOf j n ≫ homologyMapOf q n = 0
  rw [he, hz.eq_of_src (homologyMapOf v n) 0, comp_zero]

end PoincareConjecture.M76.CutGraph
