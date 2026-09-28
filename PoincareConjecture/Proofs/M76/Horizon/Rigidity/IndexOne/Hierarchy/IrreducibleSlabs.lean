import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.Geometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.IncompressibleCutIrreducibility
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RetractionFundamentalGroup
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

private theorem whole_annulus_connected_nontrivial
    {Y : Type*} [TopologicalSpace Y] {S : Set Y} (A : Ann ≃ₜ S) :
    IsPreconnected S ∧ ∀ x : S, Nontrivial (FundamentalGroup S x) := by
  obtain ⟨E, _⟩ := exists_annulus_homeomorph
    (by norm_num : (0 : ℝ) < 8) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : 4 * (1 : ℝ) < 8)
  let Q := AddCircle (4 * (8 : ℝ))
  let I := Icc (-1 : ℝ) 1
  let G : (Q × I) ≃ₜ S := E.trans A
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : ConnectedSpace I := isConnected_iff_connectedSpace.mp
    (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))
  let : ConnectedSpace S := G.connectedSpace_iff.mp inferInstance
  refine ⟨isConnected_iff_connectedSpace.mpr inferInstance |>.isPreconnected, ?_⟩
  intro x
  let z := G.symm x
  let : Nontrivial (FundamentalGroup Q z.1) :=
    (circleFundamentalGroupEquivInt (4 * (8 : ℝ)) (by norm_num) z.1).symm.injective.nontrivial
  let : Nontrivial (FundamentalGroup (Q × I) z) :=
    (FundamentalGroup.map_prodMk_left_injective z.2 z.1).nontrivial
  have h : Nontrivial (FundamentalGroup S (G z)) :=
    (FundamentalGroup.map_bijective_of_homotopyEquiv G.toHomotopyEquiv z).1.nontrivial
  simpa only [z, G.apply_symm_apply] using h

private theorem irreducible_sourceSlab_of_whole_annuli
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    {phi : C(H, H)} (hI : IsPLIrreducible e R) {u v : ℝ}
    (he : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) =
      (sourceSlab phi u v ∩ frontier R) ∪
        (sourceSurface phi (u : C) ∪ sourceSurface phi (v : C)))
    (A : Ann ≃ₜ sourceSurface phi (u : C))
    (B : Ann ≃ₜ sourceSurface phi (v : C))
    (hA : ∀ x : sourceSurface phi (u : C), Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi (u : C), X)) x))
    (hB : ∀ x : sourceSurface phi (v : C), Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi (v : C), X)) x)) :
    IsPLIrreducible e (sourceSlab phi u v) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let M : Bool → Set X := fun b => if b then sourceSurface phi (v : C)
    else sourceSurface phi (u : C)
  have hMfront (b : Bool) : M b ⊆ frontier (sourceSlab phi u v) := by
    intro x hx
    rw [hfront]
    cases b
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  obtain ⟨hconnA, hnonA⟩ := whole_annulus_connected_nontrivial A
  obtain ⟨hconnB, hnonB⟩ := whole_annulus_connected_nontrivial B
  apply hI.of_incompressible_cut he (sourceSlab_subset phi u v) M hMfront
  · intro x hx hxint
    rw [hfront] at hx
    rcases hx with hxold | hxa | hxb
    · exact (hxold.2.2 hxint).elim
    · exact ⟨false, hxa⟩
    · exact ⟨true, hxb⟩
  · intro b
    cases b
    · exact hconnA
    · exact hconnB
  · intro b x
    have hinj : Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(M b, X)) x) := by
      cases b
      · exact hA x
      · exact hB x
    refine ⟨?_, ?_⟩
    · cases b
      · exact hnonA x
      · exact hnonB x
    · let hMR := (hMfront b).trans (he.closed.frontier_subset.trans
        (sourceSlab_subset phi u v))
      have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(M b, X)) =
          (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X)).comp
            (ContinuousMap.inclusion hMR) := rfl
      rw [heq, FundamentalGroup.map_comp] at hinj
      exact Function.Injective.of_comp hinj

theorem PairedSourceGeometry.irreducible_slabs
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    {phi : C(H, H)} {a b : ℝ} (hgeom : PairedSourceGeometry e phi a b)
    (hI : IsPLIrreducible e R)
    (A : Ann ≃ₜ sourceSurface phi (a : C))
    (B : Ann ≃ₜ sourceSurface phi (b : C)) :
    ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
      IsPLIrreducible e (sourceSlab phi uv.1 uv.2) := by
  have hperiod : ((a + p : ℝ) : C) = (a : C) := by simp
  intro uv huv
  rcases huv with huv | huv
  · subst uv
    exact irreducible_sourceSlab_of_whole_annuli hI
      (hgeom.domains _ (Or.inl rfl)) (hgeom.frontiers _ (Or.inl rfl)) A B
      (hgeom.ambient_injective a (Or.inl rfl)) (hgeom.ambient_injective b (Or.inr rfl))
  · have huv' : uv = (b, a + p) := huv
    subst uv
    apply irreducible_sourceSlab_of_whole_annuli hI
      (hgeom.domains _ (Or.inr rfl)) (hgeom.frontiers _ (Or.inr rfl)) B
      (hperiod.symm ▸ A) (hgeom.ambient_injective b (Or.inr rfl))
    exact hperiod.symm ▸ hgeom.ambient_injective a (Or.inl rfl)

end PoincareConjecture.M76.HamiltonIntervalTorus
