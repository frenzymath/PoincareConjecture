import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalTerminalEndCover

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_outermost_arc_end
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
      (_hends : ∀ z, (W z : X) ∈ frontier R ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1)
      {S : Set X} {A U C : Set P2} {f : P2 → X},
      (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0} ⊆ S →
      IsFinitePLBallPair P2 A (U ∪ C) →
      IsFinitePLBallPair ℝ U (U ∩ C) →
      ContinuousOn f A → InjOn f A →
      f '' A ∩ S = f '' C → f '' A ∩ frontier E = f '' U →
      ∃ a : Bool → sphere (0 : ι → ℝ) 1, Function.Bijective a ∧
        (∀ side y, (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) : X).1 = a side) ∧
        ∃ side : Bool, f '' U ⊆
          {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side} ∪
          (fun z => (W z : X)) ''
            {z : Y × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0} := by
  intro X R E W hends S A U C f hcore hA hU hf hfi hS hfront
  have hUA : U ⊆ A := fun x hx => hA.1 (Or.inl hx)
  have hCA : C ⊆ A := fun x hx => hA.1 (Or.inr hx)
  have hfU : MapsTo f U (frontier E) := fun x hx =>
    (hfront.symm.subset ⟨x,hx,rfl⟩).2
  have hfree : Disjoint (f '' (U \ (U ∩ C)))
      ((fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0}) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    obtain ⟨w,hw,hwz⟩ := hS.subset ⟨⟨z,hUA hz.1,rfl⟩,hcore hx⟩
    have heq : w = z := hfi (hCA hw) (hUA hz.1) hwz
    exact hz.2 ⟨hz.1,heq ▸ hw⟩
  obtain ⟨a,ha,hl,_,_,_,hsides⟩ := b.exists_original_terminal_end_cover
    he hdim hi W hends
  obtain ⟨side,hside⟩ := hsides U (U ∩ C) hU f (hf.mono hUA) hfU hfree
  exact ⟨a,ha,hl,side,hside⟩

end PoincareConjecture.M76
