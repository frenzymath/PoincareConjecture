import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalCylinderEndLabels

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_annular_boundary_labels
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
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
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) :
    ∃ a : Bool → sphere (0 : ι → ℝ) 1, Function.Bijective a ∧
      ∀ side (z : Ann), depth 8 (z : P2) = (if side then 1 else -1) →
        (p z).1 = a side := by
  classical
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  have hT : p '' Ann = E ∩ D :=
    (marked_annular_image_eq_frontier_closure p hp hfront hfull hint hends).trans
      (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
        b.ball.closure_interior).symm
  let f : Ann → ↥(p '' Ann) := fun z => ⟨p z,z,z.property,rfl⟩
  have hf : Continuous f := hp.domRestrict.subtype_mk _
  have hfi : Function.Injective f := fun x y h =>
    Subtype.ext (hpi x.property y.property (congrArg Subtype.val h))
  have hfs : Function.Surjective f := by
    rintro ⟨x,z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,rfl⟩
  have hcAnn : IsCompact Ann :=
    (isCompact_Icc.prod isCompact_Icc).diff (isOpen_Ioo.prod isOpen_Ioo)
  let : CompactSpace Ann := isCompact_iff_compactSpace.mp hcAnn
  let H := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs
  obtain ⟨C,_,hCv⟩ := Dehn.Annuli.exists_selected_annulus_cylinder
  let W : (CY × J) ≃ₜ ↥(E ∩ D) :=
    (Homeomorph.Set.prod CY J).symm.trans (C.symm.trans
      (H.trans (Homeomorph.setCongr hT)))
  have hWends : ∀ z, (W z : X) ∈ frontier R ↔
      (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 := by
    intro z
    change p (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩) ∈ frontier R ↔ _
    rw [hends]
    have hh := hCv (C.symm ⟨(z.1,z.2),z.1.property,z.2.property⟩)
    rw [C.apply_symm_apply] at hh
    rw [←hh]
  let : CompactSpace CY := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin 2 → ℝ) 1)
  let : ConnectedSpace CY := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank];simp) (0 : Fin 2 → ℝ) zero_le_one)
  obtain ⟨a,ha,hlabel⟩ := b.exists_annular_endpoint_labels he hdim hi W hWends
  refine ⟨a,ha,?_⟩
  intro side z hz
  let y : CY := ⟨(C z).val.1,(C z).property.1⟩
  let t : J := ⟨if side then 1 else -1,by cases side <;> norm_num⟩
  have hCz : C z = ⟨((y : Fin 2 → ℝ),(t : ℝ)),y.property,t.property⟩ := by
    apply Subtype.ext
    exact Prod.ext rfl ((hCv z).trans hz)
  have hval : (W (y,t) : X) = p z := by
    change p (C.symm ⟨((y : Fin 2 → ℝ),(t : ℝ)),y.property,t.property⟩) = p z
    rw [←hCz,C.symm_apply_apply]
  exact (congrArg Prod.fst hval).symm.trans (hlabel side y)

end PoincareConjecture.M76
