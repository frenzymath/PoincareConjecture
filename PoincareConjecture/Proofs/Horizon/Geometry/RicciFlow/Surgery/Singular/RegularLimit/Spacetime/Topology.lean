import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Function TopologicalSpace Topology

universe u v w z

namespace PoincareConjecture.SingularRegularLimit.TwoChart

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Z) (g : Y → Z)

@[instance_reducible] def topology : TopologicalSpace Z :=
  TopologicalSpace.coinduced (Sum.elim f g) inferInstance

theorem isOpen_iff (U : Set Z) :
    @IsOpen Z (topology f g) U ↔ IsOpen (f ⁻¹' U) ∧ IsOpen (g ⁻¹' U) := Iff.rfl

theorem continuous_left : @Continuous X Z _ (topology f g) f :=
  continuous_def.mpr fun U hU => ((isOpen_iff f g U).mp hU).1

theorem continuous_right : @Continuous Y Z _ (topology f g) g :=
  continuous_def.mpr fun U hU => ((isOpen_iff f g U).mp hU).2

theorem isOpenEmbedding_left (hf : Injective f)
    (hgf : ∀ U : Set X, IsOpen U → IsOpen (g ⁻¹' (f '' U))) :
    @IsOpenEmbedding X Z _ (topology f g) f := by
  let _ := topology f g
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_left f g) hf
  intro U hU
  apply (isOpen_iff f g (f '' U)).mpr
  exact ⟨by simpa only [preimage_image_eq U hf] using hU, hgf U hU⟩

theorem isOpenEmbedding_right (hg : Injective g)
    (hfg : ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' (g '' V))) :
    @IsOpenEmbedding Y Z _ (topology f g) g := by
  let _ := topology f g
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_right f g) hg
  intro V hV
  apply (isOpen_iff f g (g '' V)).mpr
  exact ⟨hfg V hV, by simpa only [preimage_image_eq V hg] using hV⟩

theorem continuous_iff {W : Type z} [TopologicalSpace W] (h : Z → W) :
    @Continuous Z W (topology f g) _ h ↔
      Continuous (h ∘ f) ∧ Continuous (h ∘ g) := by
  let _ := topology f g
  constructor
  · intro hh
    exact ⟨hh.comp (continuous_left f g), hh.comp (continuous_right f g)⟩
  · rintro ⟨hf, hg⟩
    apply continuous_def.mpr
    intro U hU
    exact (isOpen_iff f g (h ⁻¹' U)).mpr ⟨hU.preimage hf, hU.preimage hg⟩

theorem secondCountableTopology [SecondCountableTopology X] [SecondCountableTopology Y]
    (hf : Injective f) (hg : Injective g)
    (hfg : ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' (g '' V)))
    (hgf : ∀ U : Set X, IsOpen U → IsOpen (g ⁻¹' (f '' U)))
    (hcover : ∀ z : Z, z ∈ range f ∨ z ∈ range g) :
    @SecondCountableTopology Z (topology f g) := by
  let _ := topology f g
  have hsurj : Surjective (Sum.elim f g) := by
    intro z
    rcases hcover z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr y, rfl⟩
  have hquot : IsQuotientMap (Sum.elim f g) := ⟨⟨rfl⟩, hsurj⟩
  exact hquot.secondCountableTopology
    ((isOpenEmbedding_left f g hf hgf).isOpenMap.sumElim
      (isOpenEmbedding_right f g hg hfg).isOpenMap)

theorem t2Space [T2Space X] [T2Space Y]
    (hf : Injective f) (hg : Injective g)
    (hfg : ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' (g '' V)))
    (hgf : ∀ U : Set X, IsOpen U → IsOpen (g ⁻¹' (f '' U)))
    {W : Type z} [TopologicalSpace W] [T2Space W] (τ : Z → W)
    (hτf : Continuous (τ ∘ f)) (hτg : Continuous (τ ∘ g))
    (hsep : ∀ z w : Z, ¬ (z ∈ range f ∧ w ∈ range f) →
      ¬ (z ∈ range g ∧ w ∈ range g) → τ z ≠ τ w) :
    @T2Space Z (topology f g) := by
  let _ := topology f g
  have hfopen := isOpenEmbedding_left f g hf hgf
  have hgopen := isOpenEmbedding_right f g hg hfg
  have hτ : Continuous τ := (continuous_iff f g τ).mpr ⟨hτf, hτg⟩
  constructor
  intro z w hne
  by_cases hleft : z ∈ range f ∧ w ∈ range f
  · rcases hleft with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation (fun hxy => hne (congrArg f hxy))
    exact ⟨f '' U, f '' V, hfopen.isOpenMap U hU, hfopen.isOpenMap V hV,
      mem_image_of_mem f hx, mem_image_of_mem f hy, disjoint_image_of_injective hf hdisj⟩
  · by_cases hright : z ∈ range g ∧ w ∈ range g
    · rcases hright with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
      obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation (fun hxy => hne (congrArg g hxy))
      exact ⟨g '' U, g '' V, hgopen.isOpenMap U hU, hgopen.isOpenMap V hV,
        mem_image_of_mem g hx, mem_image_of_mem g hy, disjoint_image_of_injective hg hdisj⟩
    · obtain ⟨U, V, hU, hV, hz, hw, hdisj⟩ := t2_separation (hsep z w hleft hright)
      exact ⟨τ ⁻¹' U, τ ⁻¹' V, hU.preimage hτ, hV.preimage hτ, hz, hw,
        hdisj.preimage τ⟩

end PoincareConjecture.SingularRegularLimit.TwoChart
