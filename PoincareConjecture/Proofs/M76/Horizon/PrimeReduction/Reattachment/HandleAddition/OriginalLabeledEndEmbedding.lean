import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalHalfCylinderImage
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcEnd
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcEndImage

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_embedding_of_original_labeled_end
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
      (a : Bool → sphere (0 : ι → ℝ) 1)
      (_hlabel : ∀ (s : Bool) (y : Y),
        (W (y,⟨if s then 1 else -1,by cases s <;> norm_num⟩) : X).1 = a s)
      (side : Bool),
    let B := (fun z => (W z : X)) ''
      {z : Y × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
    let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side}
    ∃ F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
      (∀ x : A, F ⟨x,Or.inl x.property⟩ = x.val.2) ∧
      F.Homotopic ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩ ∧
      ∃ H : (Y × I) ≃ₜ B,
        (∀ z : Y × I, ∃ w : Y × J, w.1 = z.1 ∧
          (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
          (H z : X) = W w) ∧
        ∃ v : C(Y,κ → ℝ), Function.Injective v ∧ (∀ y, ‖v y‖ = (3/2 : ℝ)) ∧
          (∀ y, (QuotientAddGroup.mk (v y) : (κ → ℝ) ⧸ L.toAddSubgroup) = (H (y,0) : X).2) ∧
          ∀ z : Y × I, F ⟨H z,Or.inr (H z).property⟩ =
            QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1) := by
  classical
  intro X R E W hends a hlabel side B A
  obtain ⟨B',hB',hBT,H,hHr,_,hcoords⟩ := exists_closed_half_cylinder W hends side
  have hB'B : B' = B := closed_half_cylinder_image W H side hcoords
  let HB : (Y × I) ≃ₜ B := H.trans (Homeomorph.setCongr hB'B)
  have hBc : IsClosed B := hB'B ▸ hB'
  have hBsub : B ⊆ E ∩ D := hB'B ▸ hBT
  have hHB : ∀ z, (HB z : X) ∈ frontier R ↔ (z.2 : ℝ) = 0 := hHr
  have hHBcoords : ∀ z, ∃ w, w.1 = z.1 ∧
      (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
      (HB z : X) = W w := hcoords
  obtain ⟨a',F,hFi,hFA,_,hFhom,ha',v,hvi,hvn,hv,hFv⟩ :=
    b.exists_closed_annular_end_quotient_embedding_with_lift he hdim hi hBc hBsub HB hHB
  have haa : a' = a side := by
    apply Subtype.ext
    let y : Y := Classical.choice ‹Nonempty Y›
    have hh := closed_half_cylinder_old_endpoint W HB side hHBcoords y
    exact (ha' y).symm.trans ((congrArg Prod.fst hh).trans (hlabel side y))
  let A' := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a'.val}
  have hset : A' ∪ B = A ∪ B := by simp only [A',haa,A]
  let K : ↥(A ∪ B) ≃ₜ ↥(A' ∪ B) := Homeomorph.setCongr hset.symm
  let G : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup) := F.comp ⟨K,K.continuous⟩
  refine ⟨G,hFi.comp K.injective,?_,?_,HB,hHBcoords,v,hvi,hvn,hv,?_⟩
  · intro x
    have hx : (x : X) ∈ A' := by simpa only [A',haa,A] using x.property
    exact hFA ⟨x,hx⟩
  · exact hFhom.comp (ContinuousMap.Homotopic.refl ⟨K,K.continuous⟩)
  · intro z
    exact hFv z

local notation "CY" => sphere (0 : Fin 2 → ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_embedding_of_original_labeled_end_with_image
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (W : (CY × J) ≃ₜ ↥(E ∩ D))
      (_hends : ∀ z, (W z : X) ∈ frontier R ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1)
      (a : Bool → sphere (0 : ι → ℝ) 1)
      (_hlabel : ∀ (s : Bool) (y : CY),
        (W (y,⟨if s then 1 else -1,by cases s <;> norm_num⟩) : X).1 = a s)
      (side : Bool),
    let B := (fun z => (W z : X)) ''
      {z : CY × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
    let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side}
    ∃ F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
      (∀ x : A, F ⟨x,Or.inl x.property⟩ = x.val.2) ∧
      F.Homotopic ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩ ∧
      ∃ H : (CY × I) ≃ₜ B,
        (∀ z : CY × I, ∃ w : CY × J, w.1 = z.1 ∧
          (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
          (H z : X) = W w) ∧
        ∃ v : C(CY,κ → ℝ), Function.Injective v ∧ (∀ y, ‖v y‖ = (3/2 : ℝ)) ∧
          (∀ y, (QuotientAddGroup.mk (v y) : (κ → ℝ) ⧸ L.toAddSubgroup) = (H (y,0) : X).2) ∧
          (∀ z : CY × I, F ⟨H z,Or.inr (H z).property⟩ =
            QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1)) ∧
          range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
            Metric.ball 0 (3/4))ᶜ := by
  classical
  intro X R E W hends a hlabel side B A
  obtain ⟨B',hB',hBT,H,hHr,_,hcoords⟩ := exists_closed_half_cylinder W hends side
  have hB'B : B' = B := closed_half_cylinder_image W H side hcoords
  let HB : (CY × I) ≃ₜ B := H.trans (Homeomorph.setCongr hB'B)
  have hBc : IsClosed B := hB'B ▸ hB'
  have hBsub : B ⊆ E ∩ D := hB'B ▸ hBT
  have hHB : ∀ z, (HB z : X) ∈ frontier R ↔ (z.2 : ℝ) = 0 := hHr
  have hHBcoords : ∀ z : CY × I, ∃ w : CY × J, w.1 = z.1 ∧
      (w.2 : ℝ) = (if side then 1 - (z.2 : ℝ) else (z.2 : ℝ) - 1) ∧
      (HB z : X) = W w := hcoords
  obtain ⟨a',F,hFi,hFA,_,hFhom,ha',v,hvi,hvn,hv,hFv,hFrange⟩ :=
    b.exists_closed_annular_end_quotient_embedding_with_image he hdim hi hBc hBsub HB hHB
  have haa : a' = a side := by
    apply Subtype.ext
    obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr zero_le_one :
      (sphere (0 : Fin 2 → ℝ) 1).Nonempty)
    have hh := closed_half_cylinder_old_endpoint W HB side hHBcoords ⟨y,hy⟩
    exact (ha' ⟨y,hy⟩).symm.trans ((congrArg Prod.fst hh).trans (hlabel side ⟨y,hy⟩))
  let A' := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a'.val}
  have hset : A' ∪ B = A ∪ B := by simp only [A',haa,A]
  let K : ↥(A ∪ B) ≃ₜ ↥(A' ∪ B) := Homeomorph.setCongr hset.symm
  let G : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup) := F.comp ⟨K,K.continuous⟩
  refine ⟨G,hFi.comp K.injective,?_,?_,HB,hHBcoords,v,hvi,hvn,hv,?_,?_⟩
  · intro x
    have hx : (x : X) ∈ A' := by simpa only [A',haa,A] using x.property
    exact hFA ⟨x,hx⟩
  · exact hFhom.comp (ContinuousMap.Homotopic.refl ⟨K,K.continuous⟩)
  · intro z
    exact hFv z
  · change range ((F : ↥(A' ∪ B) → _) ∘ K) = _
    rw [range_comp,K.surjective.range_eq,image_univ]
    exact hFrange

end PoincareConjecture.M76
