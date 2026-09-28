import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.RetainedRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CompressedCircleModel
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected

set_option autoImplicit false
open Set Topology Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

local instance : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩

noncomputable def componentAnnulusRim
    {X : Type*} [TopologicalSpace X] {P B S : Set X}
    (hS : S ⊆ P) (H : Ann ≃ₜ S)
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X) ∈ B) (b : Bool) : C(C32, ↥(B ∩ P)) where
  toFun z := ⟨H (annulusRimPoint b z), by
    refine ⟨(hmark _).mp ?_, hS (H _).property⟩
    cases b <;> simp [depth_annulusRimPoint]⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp H.continuous).comp (continuous_annulusRimPoint b)).subtype_mk _

theorem isOpenEmbedding_componentAnnulusRim
    {X : Type*} [TopologicalSpace X] [T2Space X] {P B S : Set X}
    [LocallyConnectedSpace P] (hS : S ⊆ P)
    (hcomponent : ∀ x ∈ S, connectedComponentIn P x = S)
    (H : Ann ≃ₜ S)
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X) ∈ B) (b : Bool) :
    IsOpenEmbedding (componentAnnulusRim hS H hmark b) := by
  let i := componentAnnulusRim hS H hmark
  have hi (s : Bool) : Function.Injective (i s) := by
    intro x y hxy
    apply injective_annulusRimPoint s
    apply H.injective
    exact Subtype.ext (congrArg (fun z : ↥(B ∩ P) => (z : X)) hxy)
  have hdis : Disjoint (range (i b)) (range (i (!b))) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have heq : annulusRimPoint (!b) y = annulusRimPoint b x :=
      H.injective (Subtype.ext (congrArg (fun z : ↥(B ∩ P) => (z : X)) hy))
    have hd := congrArg (fun z : Ann => depth 8 (z : ℝ × ℝ)) heq
    cases b <;> norm_num [depth_annulusRimPoint] at hd
  let incl : C(↥(B ∩ P), P) := ContinuousMap.inclusion inter_subset_right
  have hSopen : IsOpen (Subtype.val ⁻¹' S : Set P) := by
    let x : S := H (annulusRimPoint b 0)
    rw [← hcomponent x x.property, connectedComponentIn_eq_image (hS x.property),
      preimage_image_eq _ Subtype.val_injective]
    exact isOpen_connectedComponent
  have hrange : range (i b) =
      incl ⁻¹' (Subtype.val ⁻¹' S : Set P) ∩ (range (i (!b)))ᶜ := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(H _).property, fun hx => disjoint_left.mp hdis ⟨z, rfl⟩ hx⟩
    · rintro ⟨hxS, hxother⟩
      let y : S := ⟨x, hxS⟩
      have hy : (H (H.symm y) : X) ∈ B := by simpa using x.property.1
      have hrim := (hmark (H.symm y)).mpr hy
      have hb : depth 8 (H.symm y : ℝ × ℝ) = if b then 1 else -1 := by
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.not_true] at *
        · rcases hrim with h | h
          · exact h
          · exfalso
            obtain ⟨z, hz⟩ := (range_annulusRimPoint true).symm.subset h
            apply hxother
            refine ⟨z, Subtype.ext ?_⟩
            change (H (annulusRimPoint true z) : X) = x
            rw [hz, H.apply_symm_apply]
        · rcases hrim with h | h
          · exfalso
            obtain ⟨z, hz⟩ := (range_annulusRimPoint false).symm.subset h
            apply hxother
            refine ⟨z, Subtype.ext ?_⟩
            change (H (annulusRimPoint false z) : X) = x
            rw [hz, H.apply_symm_apply]
          · exact h
      obtain ⟨z, hz⟩ := (range_annulusRimPoint b).symm.subset hb
      refine ⟨z, Subtype.ext ?_⟩
      change (H (annulusRimPoint b z) : X) = x
      rw [hz, H.apply_symm_apply]
  exact ⟨((i b).continuous.isClosedEmbedding (hi b)).isEmbedding, hrange ▸
    (hSopen.preimage incl.continuous).inter
      (isCompact_range (i (!b)).continuous).isClosed.isOpen_compl⟩

theorem isCoveringMap_componentAnnulusRim
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    {P B S : Set X} [LocallyConnectedSpace P] (hS : S ⊆ P)
    (hcomponent : ∀ x ∈ S, connectedComponentIn P x = S)
    (H : Ann ≃ₜ S)
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X) ∈ B)
    (q : C(↥(B ∩ P), Y)) (hq : IsCoveringMap q) (b : Bool) :
    IsCoveringMap (q.comp (componentAnnulusRim hS H hmark b)) := by
  exact isLocalHomeomorph_iff_isCoveringMap.mp
    (hq.isLocalHomeomorph.comp
      (isOpenEmbedding_componentAnnulusRim hS hcomponent H hmark b).isLocalHomeomorph)

end PoincareConjecture.M76.Dehn

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_compressed_annulus_rim_circle_covering
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other})))
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    {S : Set X0} (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = S)
    (H : squareAnnulus 8 1 ≃ₜ S)
    (hmark : ∀ z : squareAnnulus 8 1,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
        (H z : X0) ∈ frontier R)
    (side : Bool) :
    IsCoveringMap (fun z : C32 =>
      (Q0 (hamiltonZeroAmbientMap psi (H (Dehn.annulusRimPoint side z)))).1.1) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let P := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}
  obtain ⟨s, F, K, B, g, hFc, hFi, _, hK, _, _, hKs, _, hgPL, _, hFg, hgP, _⟩ :=
    exists_hamiltonZero_compressed_circle_incidence e phi psi heR hA hAR hfixed hne hreg hN hfront
  have hFK (x : X0) (hx : x ∈ P) : F x ∈ K.space := hKs.symm.subset ⟨x, hx, rfl⟩
  have hgF (x : X0) (hx : x ∈ P) : g (F x) = x := hFi (hFg (F x) (hFK x hx))
  let HK : K.space ≃ₜ P := Homeomorph.ofSetInverse g F K.space P
    hgPL.continuousOn hFc.continuousOn
    (fun z hz => hgP.subset ⟨z, hz, rfl⟩) hFK hFg hgF
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : LocallyPathConnectedSpace P := HK.isQuotientMap.locallyPathConnectedSpace
  have hset : frontier R ∩ P = frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta} := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
      fun hx => ⟨hx.1, heR.closed.frontier_subset hx.1, hx.2⟩⟩
  let T := Homeomorph.setCongr hset
  let q := (hamiltonZeroSecondPhaseCircleMap psi (frontier R) theta).comp ⟨T, T.continuous⟩
  have hq : IsCoveringMap q :=
    (hamiltonZero_boundary_rim_covering_of_supported_map phi psi hAR hfixed theta hcover).comp_homeomorph T
  have h := Dehn.isCoveringMap_componentAnnulusRim hS hcomponent H hmark q hq side
  convert h using 1
  funext z
  rfl

end PoincareConjecture.M76
