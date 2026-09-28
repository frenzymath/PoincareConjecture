import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ConnectedCutGraphBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FiniteComplexHomologyDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentCycleRankBound
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomologyCount








set_option autoImplicit false
open Set Metric Geometry CategoryTheory
open scoped BigOperators
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem prescribed_cut_card_le_homology_add_zero_components
    {X κ : Type u} {ι : Type*} [TopologicalSpace X] [T2Space X]
    [Fintype κ] [DecidableEq κ] {e : ι → OpenPartialHomeomorph X V3}
    (R Q : Set X) [Fintype (ConnectedComponents Q)] [DecidableEq (ConnectedComponents Q)]
    (hR : IsCompact R) (hRPL : PLDomain e R) (hRc : IsConnected R)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (O : κ → Set X) (B : κ × Bool → Set X)
    (H : ∀ i b, S i ≃ₜ B (i,b)) (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (D : ConnectedComponents Q → Set X) (ends : κ → Bool → ConnectedComponents Q)
    (hQ : Q = R \ ⋃ i,O i) (hcQ : IsClosed Q)
    (hO : ∀ i, IsOpen (O i)) (hCR : ∀ i, closure (O i) ⊆ R)
    (hCC : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hcover : (⋃ i,closure (O i)) ∪ Q = R)
    (hD : ∀ v, IsCompact (D v) ∧ PLDomain e (D v) ∧ IsConnected (D v) ∧ D v ⊆ Q)
    (hDD : Pairwise fun v w => Disjoint (D v) (D w)) (hDcover : (⋃ v,D v) = Q)
    (hactual : ∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x)
    (hinc : ∀ i v, closure (O i) ∩ D v = ⋃ b ∈ {b | ends i b = v}, B (i,b))
    (hW : ∀ i x, (W i (x,0) : X) = H i false x ∧ (W i (x,1) : X) = H i true x) :
    Fintype.card κ + 1 ≤ Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology R 1) +
      {v | Limits.IsZero (ModTwoMayerVietoris.homology (D v) 1)}.ncard := by
  classical
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRc
  let := hRPL.finite_modTwo_homology hR 1
  have hQR : Q ⊆ R := hQ ▸ sdiff_subset
  obtain ⟨q,hqD,hqC⟩ := CutGraph.exists_closed_cut_graph_collapse R D
    (fun i => closure (O i)) (fun i b => B (i,b)) ends (fun i => S i) W
    (fun v => (hD v).1.isClosed) (fun _ => isClosed_closure) hDD hCC
    (by rw [hDcover,union_comm]; exact hcover) hinc
    (fun i b x => CutGraph.collar_port_iff_height (fun b => B (i,b)) (H i) (W i) (hW i) b x)
  have hnonempty (i : κ) : Nonempty (S i) := by
    obtain ⟨x,hx⟩ := (show (sphere (0 : V3) 1).Nonempty from
      NormedSpace.sphere_nonempty.mpr zero_le_one)
    exact ⟨(sS i).parametrization ⟨x,hx⟩⟩
  let : ∀ i, Nonempty (S i) := hnonempty
  have hport (i : κ) (b : Bool) (x : S i) :
      (W i (x,if b then 1 else 0) : X) ∈ D (ends i b) := by
    have hb : (W i (x,if b then 1 else 0) : X) ∈ B (i,b) := by
      cases b
      · simpa only [Bool.false_eq_true,if_false,(hW i x).1] using (H i false x).property
      · simpa only [if_true,(hW i x).2] using (H i true x).property
    exact ((hinc i (ends i b)).symm.subset (mem_iUnion₂.mpr ⟨b,rfl,hb⟩)).2
  obtain ⟨s,hqs⟩ := CutGraph.exists_homotopy_section_of_closed_cut_collapse R D
    (fun i => closure (O i)) (fun v => (hD v).2.1) (fun v => (hD v).2.2.1)
    (fun v => (hD v).2.2.2.trans hQR) hCR (fun i => S i) W ends hport q hqD hqC
  have hincQ (i : κ) : closure (O i) ∩ Q = B (i,false) ∪ B (i,true) := by
    ext x
    constructor
    · rintro ⟨hxC,hxQ⟩
      obtain ⟨v,hv⟩ := mem_iUnion.mp (hDcover.symm ▸ hxQ)
      obtain ⟨b,_,hb⟩ := mem_iUnion₂.mp ((hinc i v).subset ⟨hxC,hv⟩)
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    · intro hx
      have hb : ∃ b : Bool, x ∈ B (i,b) := by
        rcases hx with hx | hx
        · exact ⟨false,hx⟩
        · exact ⟨true,hx⟩
      obtain ⟨b,hb⟩ := hb
      have hh := (hinc i (ends i b)).symm.subset (mem_iUnion₂.mpr ⟨b,rfl,hb⟩)
      exact ⟨hh.1,hDcover ▸ mem_iUnion.mpr ⟨ends i b,hh.2⟩⟩
  let j : C(Q,R) := ⟨Set.inclusion hQR,continuous_inclusion _⟩
  have hj : Function.Injective (ModTwoMayerVietoris.homologyMapOf j 1) :=
    cut_inclusion_homology_injective sS R Q O B W H hQ hcQ hO hCR hCC hincQ hW
  have hzero : ModTwoMayerVietoris.homologyMapOf j 1 ≫
      ModTwoMayerVietoris.homologyMapOf q 1 = 0 :=
    CutGraph.cut_graph_homology_comp_zero R Q hQR D hactual ends q hqD 1 one_ne_zero
  have hvertices : ∀ v, ∃ x, (q x : CutGraph.Ambient (ConnectedComponents Q) κ) =
      CutGraph.vertex v := by
    intro v
    obtain ⟨x,hx⟩ := (hD v).2.2.1.nonempty
    exact ⟨⟨x,hQR ((hD v).2.2.2 hx)⟩,hqD v _ hx⟩
  have hcycle := CutGraph.connected_cycle_rank_of_vertices_reached ends q hvertices
  have hbound := CutGraph.component_cycle_rank_le ends j q s hqs hj hzero
  have hsum := PLDomain.finrank_disjoint_components Q D (fun v => (hD v).1)
    (fun v => (hD v).2.1) hDD hDcover 1
  rw [hsum] at hbound
  have hcount := PLDomain.card_le_zero_homology_components_add_rank_sum D
    (fun v => (hD v).1) (fun v => (hD v).2.1) 1
  omega

end PoincareConjecture.M76
