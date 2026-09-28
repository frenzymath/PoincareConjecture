import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent
set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

structure RawSourceCrossing {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (f : E → X)
    (S : Set E) (R : Set X) (x y : E) where
  chart : OpenPartialHomeomorph X V3
  left : Set E
  right : Set E
  left_subset : left ⊆ S
  right_subset : right ⊆ S
  left_open : IsOpen ((Subtype.val : S → E) ⁻¹' left)
  right_open : IsOpen ((Subtype.val : S → E) ⁻¹' right)
  disjoint : Disjoint left right
  labels : (x ∈ left ∧ y ∈ right) ∨ (x ∈ right ∧ y ∈ left)
  point : f x ∈ chart.source
  left_embedding : IsEmbedding (fun z : left ↦ f z)
  right_embedding : IsEmbedding (fun z : right ↦ f z)
  whole_preimage : S ∩ f ⁻¹' chart.source = left ∪ right
  compatible : ∀ k, (e k).symm.trans chart ∈ piecewiseAffineGroupoid V3
  left_image : ∀ z ∈ chart.source, z ∈ f '' left ↔ chart z 0 = 0 ∧ z ∈ R
  right_image : ∀ z ∈ chart.source, z ∈ f '' right ↔ chart z 1 = 0 ∧ z ∈ R
  region : chart.source ⊆ interior R ∨
    ((∀ z ∈ chart.source, z ∈ R ↔ 0 ≤ chart z 2) ∧
      ∀ z ∈ chart.source, z ∈ frontier R ↔ chart z 2 = 0)

theorem nonempty_rawSourceCrossing_of_twoBranchWindow
    {E X Y ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set E} (d : E → Y) (p : Y → X)
    (hd : IsEmbedding (fun z : S ↦ d z))
    {R : Set X} {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : p (d x) = p (d y)) (w : TwoBranchWindow p)
    (T : OpenPartialHomeomorph X V3)
    (hlabels : (d x ∈ w.left.source ∧ d y ∈ w.right.source) ∨
      (d x ∈ w.right.source ∧ d y ∈ w.left.source))
    (hxT : p (d x) ∈ T.source) (hTw : T.source ⊆ w.target)
    (hcompat : ∀ k, (e k).symm.trans T ∈ piecewiseAffineGroupoid V3)
    (hleft : ∀ z ∈ T.source, z ∈ p '' (d '' S ∩ w.left.source) ↔
      T z 0 = 0 ∧ z ∈ R)
    (hright : ∀ z ∈ T.source, z ∈ p '' (d '' S ∩ w.right.source) ↔
      T z 1 = 0 ∧ z ∈ R)
    (hregion : T.source ⊆ interior R ∨
      ((∀ z ∈ T.source, z ∈ R ↔ 0 ≤ T z 2) ∧
        ∀ z ∈ T.source, z ∈ frontier R ↔ T z 2 = 0)) :
    Nonempty (RawSourceCrossing e (p ∘ d) S R x y) := by
  let L : Set E := (S ∩ d ⁻¹' w.left.source) ∩ (p ∘ d) ⁻¹' T.source
  let U : Set E := (S ∩ d ⁻¹' w.right.source) ∩ (p ∘ d) ⁻¹' T.source
  have hbranch (B : OpenPartialHomeomorph Y X) (hB : (B : Y → X) = p) :
      IsOpen ((Subtype.val : S → E) ⁻¹'
        ((S ∩ d ⁻¹' B.source) ∩ (p ∘ d) ⁻¹' T.source)) ∧
      IsEmbedding (fun z : ((S ∩ d ⁻¹' B.source) ∩ (p ∘ d) ⁻¹' T.source : Set E) ↦
        p (d z)) := by
    constructor
    · have heq : (Subtype.val : S → E) ⁻¹'
          ((S ∩ d ⁻¹' B.source) ∩ (p ∘ d) ⁻¹' T.source) =
          (fun z : S ↦ d z) ⁻¹' (B.source ∩ B ⁻¹' T.source) := by
        ext z
        simp only [mem_preimage, mem_inter_iff, z.property, true_and, Function.comp_apply, hB]
      rw [heq]
      exact (B.isOpen_inter_preimage T.open_source).preimage hd.continuous
    · let A : Set E := (S ∩ d ⁻¹' B.source) ∩ (p ∘ d) ⁻¹' T.source
      have hs : A ⊆ S := fun _ h ↦ h.1.1
      have hd' : IsEmbedding (fun z : A ↦ d z) := hd.comp (IsEmbedding.inclusion hs)
      have hdB : IsEmbedding (fun z : A ↦ (⟨d z, z.property.1.2⟩ : B.source)) :=
        hd'.codRestrict _ _
      have hem : IsEmbedding (fun z : A ↦ B (d z)) := B.isEmbedding_restrict.comp hdB
      simpa only [hB] using hem
  have hL := hbranch w.left w.left_eq
  have hU := hbranch w.right w.right_eq
  have hxyT : p (d y) ∈ T.source := hxy ▸ hxT
  refine ⟨⟨T, L, U, fun _ h ↦ h.1.1, fun _ h ↦ h.1.1,
    hL.1, hU.1, ?_, ?_, hxT, hL.2, hU.2, ?_, hcompat, ?_, ?_, hregion⟩⟩
  · exact disjoint_left.mpr (fun z hzL hzU ↦
      disjoint_left.mp w.disjoint hzL.1.2 hzU.1.2)
  · rcases hlabels with ⟨hxL, hyU⟩ | ⟨hxU, hyL⟩
    · exact Or.inl ⟨⟨⟨hx, hxL⟩, hxT⟩, ⟨⟨hy, hyU⟩, hxyT⟩⟩
    · exact Or.inr ⟨⟨⟨hx, hxU⟩, hxT⟩, ⟨⟨hy, hyL⟩, hxyT⟩⟩
  · ext z
    constructor
    · rintro ⟨hz, hzT⟩
      rcases w.whole_preimage.subset (hTw hzT) with hzL | hzU
      · exact Or.inl ⟨⟨hz, hzL⟩, hzT⟩
      · exact Or.inr ⟨⟨hz, hzU⟩, hzT⟩
    · rintro (hz | hz) <;> exact ⟨hz.1.1, hz.2⟩
  · intro z hz
    rw [← hleft z hz]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨d a, ⟨⟨a, ha.1.1, rfl⟩, ha.1.2⟩, rfl⟩
    · rintro ⟨_, ⟨⟨a, ha, rfl⟩, haL⟩, rfl⟩
      exact ⟨a, ⟨⟨ha, haL⟩, hz⟩, rfl⟩
  · intro z hz
    rw [← hright z hz]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨d a, ⟨⟨a, ha.1.1, rfl⟩, ha.1.2⟩, rfl⟩
    · rintro ⟨_, ⟨⟨a, ha, rfl⟩, haU⟩, rfl⟩
      exact ⟨a, ⟨⟨ha, haU⟩, hz⟩, rfl⟩

end PoincareConjecture.M76.Dehn.Annuli
