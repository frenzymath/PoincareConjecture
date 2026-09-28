import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalTerminalFreeArcEnd
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalLabeledEndEmbedding

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_enclosing_arc_end
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : ContinuousOn p Ann) (hpi : InjOn p Ann)
    (hfront : p '' Ann ⊆ frontier D)
    (hfull : frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ p '' Ann)
    (hint : p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
      interior (latticeHandleDomain ι κ L))
    (hends : ∀ z : Ann, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    {n : ℕ} (P : Polygon P2 (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P)
    (hdepth : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
    (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ {S : Set X} {A U C : Set P2} {f : P2 → X},
      p '' P.boundary ℝ ⊆ S →
      IsFinitePLBallPair P2 A (U ∪ C) →
      IsFinitePLBallPair ℝ U (U ∩ C) →
      ContinuousOn f A → InjOn f A →
      f '' A ∩ S = f '' C → f '' A ∩ frontier E = f '' U →
    ∃ W : (CY × J) ≃ₜ ↥(E ∩ D),
      (∀ z, (W z : X) ∈ frontier R ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1) ∧
      (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0} = p '' P.boundary ℝ ∧
      ∃ a : Bool → sphere (0 : ι → ℝ) 1, Function.Bijective a ∧
        (∀ side y, (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) : X).1 = a side) ∧
        ∃ side : Bool,
        let B := (fun z => (W z : X)) ''
          {z : CY × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
        let Old := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side}
        let End := Old ∪ B
        IsCompact End ∧ f '' U ⊆ End ∧ p '' P.boundary ℝ ⊆ End ∧
        ∃ F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
          (∀ x : Old, F ⟨x,Or.inl x.property⟩ = x.val.2) ∧
          F.Homotopic ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩ ∧
          ∃ H : (CY × I) ≃ₜ B,
            range (fun y => (H (y,1) : X)) = p '' P.boundary ℝ ∧
            (∀ z : CY × I, ∃ w : CY × J, w.1 = z.1 ∧
              (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
              (H z : X) = W w) ∧
            ∃ v : C(CY,κ → ℝ), Function.Injective v ∧
              (∀ y, ‖v y‖ = (3/2 : ℝ)) ∧
              (∀ z : CY × I, F ⟨H z,Or.inr (H z).property⟩ =
                QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1)) ∧
              range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
                Metric.ball 0 (3/4))ᶜ := by
  classical
  intro X R E S A U C f hPS hA hU hf hfi hS hF
  let : CompactSpace CY := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin 2 → ℝ) 1)
  let : ConnectedSpace CY := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank];simp) (0 : Fin 2 → ℝ) zero_le_one)
  obtain ⟨W0,hann,hWends,hcore⟩ := b.exists_enclosing_circle_annular_coordinates
    he hdim hi p hp hpi hfront hfull hint hends P hP hPi hdepth hencl
  let W : (CY × J) ≃ₜ ↥(E ∩ D) := W0.trans (Homeomorph.setCongr hann)
  have hWe : ∀ z, (W z : X) ∈ frontier R ↔
      (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 := hWends
  have hWc : (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0} = p '' P.boundary ℝ := hcore
  obtain ⟨a,ha,hal,side,hside⟩ := b.exists_original_outermost_arc_end
    he hdim hi W hWe (hWc.subset.trans hPS) hA hU hf hfi hS hF
  refine ⟨W,hWe,hWc,a,ha,hal,side,?_⟩
  intro B Old End
  obtain ⟨F,hFi,hFO,hFhom,H,hH,v,hvi,hvn,_,hFv,hFrange⟩ :=
    b.exists_embedding_of_original_labeled_end_with_image he hdim hi W hWe a hal side
  have hEcompact : IsCompact E := (b.closed_complement_geometry he hdim hi).1
  have hOc : IsClosed Old :=
    (isClosed_closure.inter isClosed_frontier).inter (isClosed_eq continuous_fst continuous_const)
  have hOK : IsCompact Old := hEcompact.of_isClosed_subset hOc (fun _ hx => hx.1.1)
  have hHr : range (fun z => (H z : X)) = B := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (H z).property
    · intro hx; exact ⟨H.symm ⟨x,hx⟩,congrArg Subtype.val (H.apply_symm_apply _)⟩
  have hBK : IsCompact B := hHr ▸ isCompact_range (continuous_subtype_val.comp H.continuous)
  have hPE : p '' P.boundary ℝ ⊆ End := by
    rw [←hWc]
    rintro x ⟨z,hz,rfl⟩
    apply Or.inr
    refine ⟨z,?_,rfl⟩
    change (z.2 : ℝ) = 0 at hz
    cases side <;> simp [hz]
  have hHcore : range (fun y => (H (y,1) : X)) = p '' P.boundary ℝ := by
    rw [←hWc]
    apply Subset.antisymm
    · rintro x ⟨y,rfl⟩
      obtain ⟨w,_,hwt,hw⟩ := hH (y,1)
      refine ⟨w,?_,hw.symm⟩
      change (w.2 : ℝ) = 0
      cases side <;> simpa using hwt
    · rintro x ⟨z,hz,rfl⟩
      obtain ⟨w,hwf,hwt,hw⟩ := hH (z.1,1)
      have hw0 : (w.2 : ℝ) = 0 := by cases side <;> simpa using hwt
      have hwz : w = z := Prod.ext hwf (Subtype.ext (hw0.trans hz.symm))
      exact ⟨z.1,hw.trans (congrArg (fun w => (W w : X)) hwz)⟩
  exact ⟨hOK.union hBK,hside,hPE,F,hFi,hFO,hFhom,H,hHcore,hH,v,hvi,hvn,hFv,hFrange⟩

end PoincareConjecture.M76
