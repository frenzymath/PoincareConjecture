import PoincareConjecture.Proofs.M53.Prop15_12_SubspaceTransport
import PoincareConjecture.Proofs.M53.Prop15_12_CylinderSurface
import PoincareConjecture.Proofs.M53.Mathlib.ZeroSliceChart

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set Topology
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

theorem surfaceInclusion_chartCylinder_homology_isIso
    {X E : Type u} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set X) (e : OpenPartialHomeomorph X (E × ℝ))
    (hS : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (D : Set E) (hD : IsCompact D) (t : ℝ) (ht : 0 < t)
    (hKt : D ×ˢ Icc (-t) t ⊆ e.target) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap
      (ContinuousMap.inclusion
        (subset_union_left : S ⊆ S ∪ (e.symm '' (D ×ˢ Icc (-t) t))ᶜ))
      (A := (Subtype.val : S → X) ⁻¹' (e.symm '' (D ×ˢ Icc (-t) t))ᶜ)
      (B := (Subtype.val : (S ∪ (e.symm '' (D ×ˢ Icc (-t) t))ᶜ : Set X) → X) ⁻¹'
        (e.symm '' (D ×ˢ Icc (-t) t))ᶜ) (fun _ hx => hx)) n) := by
  let K := D ×ˢ Icc (-t) t
  let KX := e.symm '' K
  let L := KXᶜ
  let A := S ∪ L
  let Q := cylinderSliceExterior D t
  let U := e.target
  let AV : Set U := (Subtype.val : U → E × ℝ) ⁻¹' Q
  let LV : Set U := (Subtype.val : U → E × ℝ) ⁻¹' Kᶜ
  let f : C(U, X) := ⟨fun z => e.symm z, e.symm.continuousOn.domRestrict⟩
  let g : C(U, E × ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : IsOpenEmbedding f := e.symm.isOpenEmbedding_restrict
  have hg : IsOpenEmbedding g := e.open_target.isOpenEmbedding_subtypeVal
  have hK : IsCompact K := hD.prod isCompact_Icc
  have hKX : IsCompact KX := hK.image_of_continuousOn (e.symm.continuousOn.mono hKt)
  have hKXs : KX ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  have hfKr : KX ⊆ range f := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨⟨z, hKt hz⟩, rfl⟩
  have hgKr : K ⊆ range g := fun z hz => ⟨⟨z, hKt hz⟩, rfl⟩
  have hKmem (z : U) : f z ∈ KX ↔ z.val ∈ K := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwz := e.symm.injOn (hKt hw) z.property heq
      exact hwz ▸ hw
    · exact fun hz => ⟨z.val, hz, rfl⟩
  have hfL (z : U) : z ∈ LV ↔ f z ∈ L := (not_congr (hKmem z)).symm
  have hfA (z : U) : z ∈ AV ↔ f z ∈ A := by
    have hs : f z ∈ S ↔ z.val.2 = 0 := by
      change e.symm z.val ∈ S ↔ z.val.2 = 0
      simpa only [e.right_inv z.property] using
        hS (e.symm z.val) (e.map_target z.property)
    exact or_congr hs.symm (hfL z)
  let fA := (f.restrictPreimage A).comp
    (ContinuousMap.inclusion (fun z hz => (hfA z).mp hz))
  let gA := (g.restrictPreimage Q).comp (ContinuousMap.inclusion (fun _ hz => hz))
  let LA : Set A := (Subtype.val : A → X) ⁻¹' L
  let LQ : Set Q := (Subtype.val : Q → E × ℝ) ⁻¹' Kᶜ
  let LAV : Set AV := (Subtype.val : AV → U) ⁻¹' LV
  let F := integralRelativeMap fA (A := LAV) (B := LA)
    (fun z hz => (hfL z.val).mp hz)
  let G := integralRelativeMap gA (A := LAV) (B := LQ) (fun _ hz => hz)
  let : IsIso (homologyMap F n) :=
    integralRelativeMap_subspace_isIso_of_closed_support f hf hfA hfL
      hKX.isClosed hfKr Subset.rfl n
  let : IsIso (homologyMap G n) :=
    integralRelativeMap_subspace_isIso_of_closed_support g hg
      (A := AV) (A' := Q) (B := LV) (B' := Kᶜ)
      (fun _ => Iff.rfl) (fun _ => Iff.rfl) hK.isClosed hgKr Subset.rfl n
  let P := e.zeroSliceDomain
  let R : Set P := (Subtype.val : P → E) ⁻¹' Dᶜ
  let LS : Set S := (Subtype.val : S → X) ⁻¹' L
  let p : C(P, E) := ⟨Subtype.val, continuous_subtype_val⟩
  let s := e.zeroSliceMap S hS
  let j : C(S, A) := ContinuousMap.inclusion subset_union_left
  let k : C(P, AV) :=
    ⟨fun z => ⟨⟨(z.val, 0), z.property⟩, Or.inl rfl⟩, by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.prodMk continuous_const⟩
  have hsrel (z : P) : z ∈ R ↔ s z ∈ LS := by
    change z.val ∉ D ↔ f ⟨(z.val, 0), z.property⟩ ∉ KX
    rw [hKmem]
    constructor
    · exact fun hz hKz => hz hKz.1
    · intro hz hDz
      exact hz ⟨hDz, neg_nonpos.mpr ht.le, ht.le⟩
  let Pm := integralRelativeMap p (A := R) (B := Dᶜ) (fun _ hz => hz)
  let Sm := integralRelativeMap s (A := R) (B := LS) (fun z hz => (hsrel z).mp hz)
  let J := integralRelativeMap j (A := LS) (B := LA) (fun _ hz => hz)
  let H := integralRelativeMap k (A := R) (B := LAV) (fun _ hz hKz => hz hKz.1)
  let C := integralRelativeMap (cylinderSurfaceMap D t) (A := Dᶜ) (B := LQ)
    (fun _ hz hKz => hz hKz.1)
  have hDrange : D ⊆ range p := by
    intro z hz
    exact ⟨⟨z, hKt ⟨hz, neg_nonpos.mpr ht.le, ht.le⟩⟩, rfl⟩
  let : IsIso (homologyMap Pm n) := integralRelativeMap_isIso_of_closed_support p
    e.isOpen_zeroSliceDomain.isOpenEmbedding_subtypeVal (fun _ => Iff.rfl)
    hD.isClosed hDrange Subset.rfl n
  have hKSrange : (Subtype.val : S → X) ⁻¹' KX ⊆ range s := by
    intro z hz
    exact (e.mem_range_zeroSliceMap S hS z).mpr (hKXs hz)
  let : IsIso (homologyMap Sm n) := integralRelativeMap_isIso_of_closed_support s
    (e.isOpenEmbedding_zeroSliceMap S hS) hsrel
    (hKX.isClosed.preimage continuous_subtype_val) hKSrange Subset.rfl n
  let : IsIso (homologyMap C n) := cylinderSurfaceMap_relative_homology_isIso D t
    hD.isClosed ht n
  have hleft : Sm ≫ J = H ≫ F := by
    dsimp only [Sm, J, H, F]
    rw [integralRelativeMap_comp s j (A := R) (B := LS) (D := LA)
      (fun z hz => (hsrel z).mp hz) (fun _ hz => hz),
      integralRelativeMap_comp k fA (A := R) (B := LAV) (D := LA)
        (fun _ hz hKz => hz hKz.1) (fun z hz => (hfL z.val).mp hz)]
    rfl
  have hright : Pm ≫ C = H ≫ G := by
    dsimp only [Pm, C, H, G]
    rw [integralRelativeMap_comp p (cylinderSurfaceMap D t) (A := R) (B := Dᶜ) (D := LQ)
      (fun _ hz => hz) (fun _ hz hKz => hz hKz.1),
      integralRelativeMap_comp k gA (A := R) (B := LAV) (D := LQ)
        (fun _ hz hKz => hz hKz.1) (fun _ hz => hz)]
    rfl
  have hleftH := congrArg (fun q => homologyMap q n) hleft
  have hrightH := congrArg (fun q => homologyMap q n) hright
  rw [homologyMap_comp, homologyMap_comp] at hleftH hrightH
  let : IsIso (homologyMap H n ≫ homologyMap G n) := by
    rw [← hrightH]
    infer_instance
  let : IsIso (homologyMap H n) := IsIso.of_isIso_comp_right
    (homologyMap H n) (homologyMap G n)
  let : IsIso (homologyMap Sm n ≫ homologyMap J n) := by
    rw [hleftH]
    infer_instance
  exact IsIso.of_isIso_comp_left (homologyMap Sm n) (homologyMap J n)

end PoincareConjecture.Proofs.M53
