import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalCylinderEndLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalClosedEndCover

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_terminal_end_cover
    {ι κ α Y : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace Y] [ConnectedSpace Y] [Nonempty Y] [CompactSpace Y]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (W : (Y × J) ≃ₜ ↥(E ∩ D))
      (_hends : ∀ z, (W z : X) ∈ frontier R ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1),
    let core := (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0}
    ∃ a : Bool → sphere (0 : ι → ℝ) 1, Function.Bijective a ∧
      (∀ side y, (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) : X).1 = a side) ∧
      let B := fun side : Bool => (fun z => (W z : X)) ''
        {z : Y × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
      let End := fun side : Bool =>
        {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side} ∪ B side
      (∀ side, IsClosed (End side)) ∧ End false ∪ End true = frontier E ∧
        End false ∩ End true = core ∧
        ∀ (U q : Set (ℝ × ℝ)), IsFinitePLBallPair ℝ U q →
          ∀ f : (ℝ × ℝ) → X, ContinuousOn f U → MapsTo f U (frontier E) →
            Disjoint (f '' (U \ q)) core → ∃ side, f '' U ⊆ End side := by
  classical
  intro X R E W hends core
  obtain ⟨a,ha,halabel⟩ := b.exists_annular_endpoint_labels he hdim hi W hends
  refine ⟨a,ha,halabel,?_⟩
  intro B End
  let A := E ∩ frontier R
  have hA : IsClosed A := isClosed_closure.inter isClosed_frontier
  have hWends : ∀ z, (W z : X) ∈ A ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 :=
    fun z => (and_iff_right (W z).property.1).trans (hends z)
  have hcover : A ∪ (E ∩ D) = frontier E := by
    obtain ⟨_,_,_,hcontact,_,_,hfront⟩ := b.closed_complement_geometry he hdim hi
    rw [hfront,←hcontact]
    exact union_comm _ _
  let p : C(X,ι → ℝ) := ⟨Prod.fst,continuous_fst⟩
  let av : Bool → (ι → ℝ) := fun side => a side
  have hav : Function.Injective av := fun i j h => ha.1 (Subtype.ext h)
  have hpa : ∀ x ∈ A, p x = av false ∨ p x = av true := by
    intro x hx
    have hxS : x.1 ∈ sphere (0 : ι → ℝ) 1 := by
      have hh := hx.2
      change x ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
        (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) at hh
      rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero] at hh
      exact hh.1
    obtain ⟨side,hside⟩ := ha.2 ⟨x.1,hxS⟩
    have hv := (congrArg Subtype.val hside).symm
    cases side
    · exact Or.inl hv
    · exact Or.inr hv
  obtain ⟨hclosed,hunion,hinter⟩ := closed_cylinder_end_cover hA W hcover hWends p av hav hpa halabel
  change (∀ side, IsClosed (End side)) at hclosed
  change End false ∪ End true = frontier E at hunion
  change End false ∩ End true = core at hinter
  refine ⟨hclosed,hunion,hinter,?_⟩
  intro U q hU f hf hfF hfree
  have hh := original_arc_image_subset_one_closed_end (hclosed false) (hclosed true)
    hinter hU hf (fun x hx => hunion.symm.subset (hfF hx)) hfree
  exact hh.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)

end PoincareConjecture.M76
