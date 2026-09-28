import PoincareConjecture.Proofs.M76.Mathlib.LinearImageQuadrantPatches












set_option autoImplicit false

open Set Geometry RectangleCornerArcs CoordinateHalfBoxes CoordinateFourRegions

namespace Set





theorem mem_marked_arc_iff_of_selected_subset {X ι : Type*}
    (arc : ι → Set X) {d : Set X} {p q : X} (i : ι)
    (hp : p ∈ d) (hd : d ⊆ arc i) (hq : q ∉ d)
    (hpair : Pairwise (fun k l => arc k ∩ arc l = {p, q})) :
    ∀ k (x : d), (x : X) ∈ arc k ↔ k = i ∨ (x : X) = p := by
  classical
  intro k x
  by_cases hki : k = i
  · subst k
    exact iff_of_true (hd x.property) (Or.inl rfl)
  · constructor
    · intro hx
      rcases (hpair hki).subset ⟨hx, hd x.property⟩ with hxp | hxq
      · exact Or.inr hxp
      · exact (hq (hxq ▸ x.property)).elim
    · rintro (hki' | hxp)
      · exact (hki hki').elim
      · rw [hxp]
        exact ((hpair hki).symm.subset (Or.inl rfl)).1

end Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem SourcePoleQuadrantData.horizontal_axis_subset_signed_arc
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {A : E →ₗ[ℝ] ℝ}
    {t z : ℝ} (h : SourcePoleQuadrantData ψ F S g p q A t z)
    (source : Bool × Bool → Set E)
    (hlink : ∀ i : Bool, source (true, i) =
      (F ∩ S) ∩ {x | if i then A x ≤ 0 else 0 ≤ A x})
    (hheight : ∀ x : ℝ × ℝ, A (ψ x) = x.1)
    (i : Bool) (ht : if i then t ≤ 0 else 0 ≤ t) :
    ψ '' (uIcc 0 t ×ˢ {0}) ⊆ source (true, i) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (hlink i).symm.subset
  refine ⟨h.horizontal_subset ⟨x, hx, rfl⟩, ?_⟩
  change if i then A (ψ x) ≤ 0 else 0 ≤ A (ψ x)
  rw [hheight]
  have hxt : x.1 ∈ uIcc 0 t := hx.1
  cases i
  · rw [uIcc_of_le ht] at hxt
    exact hxt.1
  · rw [uIcc_of_ge ht] at hxt
    exact hxt.2






theorem SourcePoleQuadrantData.vertical_axis_map_data
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {A : E →ₗ[ℝ] ℝ}
    {t z : ℝ} (h : SourcePoleQuadrantData ψ F S g p q A t z)
    {e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)} {T : Set ((ℝ × ℝ) × ℝ)} {i : Bool × Bool}
    (hI : LinearImageQuadrantData ψ e T p t z i)
    (source : Bool × Bool → Set E) (j : Bool)
    (hsource : ψ '' ({0} ×ˢ uIcc 0 z) ⊆ source (false, j))
    (hsourcePair : Pairwise (fun k l => source k ∩ source l = {p, q}))
    {other : (ℝ × ℝ) × ℝ}
    (htargetPair : Pairwise (fun k l => arc T k ∩ arc T l = {e p, other}))
    {V : Set ((ℝ × ℝ) × ℝ)} (hother : other ∉ V)
    (himageV : e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ⊆ V) :
    (e.toHomeomorph.image (ψ '' ({0} ×ˢ uIcc 0 z))).IsFinitePL ∧
      (∀ x : ψ '' ({0} ×ˢ uIcc 0 z),
        (e.toHomeomorph.image (ψ '' ({0} ×ˢ uIcc 0 z)) x : (ℝ × ℝ) × ℝ) = e x) ∧
      (∀ x : ψ '' ({0} ×ˢ uIcc 0 z),
        (e.toHomeomorph.image (ψ '' ({0} ×ˢ uIcc 0 z)) x : (ℝ × ℝ) × ℝ) = e p ↔
          (x : E) = p) ∧
      (∀ x : ψ '' ({0} ×ˢ uIcc 0 z),
        (e.toHomeomorph.image (ψ '' ({0} ×ˢ uIcc 0 z)) x : (ℝ × ℝ) × ℝ) = e (ψ (0, z)) ↔
          (x : E) = ψ (0, z)) ∧
      (∀ k (x : ψ '' ({0} ×ˢ uIcc 0 z)),
        (x : E) ∈ source k ↔ k = (false, j) ∨ (x : E) = p) ∧
      ∀ k (x : ψ '' ({0} ×ˢ uIcc 0 z)),
        (e.toHomeomorph.image (ψ '' ({0} ×ˢ uIcc 0 z)) x : (ℝ × ℝ) × ℝ) ∈ arc T k ↔
          k = (false, i.2) ∨ (x : E) = p := by
  have hvD : ψ '' ({0} ×ˢ uIcc 0 z) ⊆ ψ '' (uIcc 0 t ×ˢ uIcc 0 z) := by
    apply image_mono
    rintro x ⟨hx, hy⟩
    exact ⟨hx ▸ left_mem_uIcc, hy⟩
  have hp : p ∈ ψ '' ({0} ×ˢ uIcc 0 z) := h.vertical.1 (Or.inl rfl)
  have havoid : other ∉ e '' (ψ '' ({0} ×ˢ uIcc 0 z)) :=
    fun hx => hother (himageV (image_mono hvD hx))
  have hsrc := mem_marked_arc_iff_of_selected_subset source (false, j) hp
    hsource h.vertical_other_notMem hsourcePair
  have htgt := mem_marked_arc_iff_of_selected_subset (arc T) (false, i.2)
    (mem_image_of_mem e hp) hI.vertical_arc havoid htargetPair
  refine ⟨hI.vertical_PL, fun _ => rfl, ?_, ?_, hsrc, ?_⟩
  · intro x
    change e (x : E) = e p ↔ (x : E) = p
    exact e.injective.eq_iff
  · intro x
    change e (x : E) = e (ψ (0, z)) ↔ (x : E) = ψ (0, z)
    exact e.injective.eq_iff
  · intro k x
    rw [htgt k (e.toHomeomorph.image _ x)]
    change (k = (false, i.2) ∨ e (x : E) = e p) ↔ k = (false, i.2) ∨ (x : E) = p
    exact or_congr Iff.rfl e.injective.eq_iff






theorem SourcePoleQuadrantData.horizontal_axis_map_data
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {A : E →ₗ[ℝ] ℝ}
    {t z : ℝ} (h : SourcePoleQuadrantData ψ F S g p q A t z)
    {e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)} {T : Set ((ℝ × ℝ) × ℝ)} {i : Bool × Bool}
    (hI : LinearImageQuadrantData ψ e T p t z i)
    (source : Bool × Bool → Set E) (j : Bool)
    (hsource : ψ '' (uIcc 0 t ×ˢ {0}) ⊆ source (true, j))
    (hsourcePair : Pairwise (fun k l => source k ∩ source l = {p, q}))
    {other : (ℝ × ℝ) × ℝ}
    (htargetPair : Pairwise (fun k l => arc T k ∩ arc T l = {e p, other}))
    {V : Set ((ℝ × ℝ) × ℝ)} (hother : other ∉ V)
    (himageV : e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ⊆ V) :
    (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ {0}))).IsFinitePL ∧
      (∀ x : ψ '' (uIcc 0 t ×ˢ {0}),
        (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ {0})) x : (ℝ × ℝ) × ℝ) = e x) ∧
      (∀ x : ψ '' (uIcc 0 t ×ˢ {0}),
        (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ {0})) x : (ℝ × ℝ) × ℝ) = e p ↔
          (x : E) = p) ∧
      (∀ x : ψ '' (uIcc 0 t ×ˢ {0}),
        (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ {0})) x : (ℝ × ℝ) × ℝ) = e (ψ (t, 0)) ↔
          (x : E) = ψ (t, 0)) ∧
      (∀ k (x : ψ '' (uIcc 0 t ×ˢ {0})),
        (x : E) ∈ source k ↔ k = (true, j) ∨ (x : E) = p) ∧
      ∀ k (x : ψ '' (uIcc 0 t ×ˢ {0})),
        (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ {0})) x : (ℝ × ℝ) × ℝ) ∈ arc T k ↔
          k = (true, i.1) ∨ (x : E) = p := by
  have hhD : ψ '' (uIcc 0 t ×ˢ {0}) ⊆ ψ '' (uIcc 0 t ×ˢ uIcc 0 z) := by
    apply image_mono
    rintro x ⟨hx, hy⟩
    exact ⟨hx, hy ▸ left_mem_uIcc⟩
  have hp : p ∈ ψ '' (uIcc 0 t ×ˢ {0}) := h.horizontal.1 (Or.inl rfl)
  have havoid : other ∉ e '' (ψ '' (uIcc 0 t ×ˢ {0})) :=
    fun hx => hother (himageV (image_mono hhD hx))
  have hsrc := mem_marked_arc_iff_of_selected_subset source (true, j) hp
    hsource h.horizontal_other_notMem hsourcePair
  have htgt := mem_marked_arc_iff_of_selected_subset (arc T) (true, i.1)
    (mem_image_of_mem e hp) hI.horizontal_arc havoid htargetPair
  refine ⟨hI.horizontal_PL, fun _ => rfl, ?_, ?_, hsrc, ?_⟩
  · intro x
    change e (x : E) = e p ↔ (x : E) = p
    exact e.injective.eq_iff
  · intro x
    change e (x : E) = e (ψ (t, 0)) ↔ (x : E) = ψ (t, 0)
    exact e.injective.eq_iff
  · intro k x
    rw [htgt k (e.toHomeomorph.image _ x)]
    change (k = (true, i.1) ∨ e (x : E) = e p) ↔ k = (true, i.1) ∨ (x : E) = p
    exact or_congr Iff.rfl e.injective.eq_iff

end Geometry

namespace RectangleCornerArcs



def axisInterval (horizontal : Bool) (a : ℝ) : Set (ℝ × ℝ) :=
  if horizontal then uIcc 0 a ×ˢ {0} else {0} ×ˢ uIcc 0 a



theorem axisInterval_subset_base (horizontal : Bool) {a r : ℝ}
    (hr : 0 ≤ r) (ha : |a| ≤ r) : axisInterval horizontal a ⊆ base r := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr, hr⟩
  have hI : uIcc 0 a ⊆ Icc (-r) r := uIcc_subset_Icc hzero (abs_le.mp ha)
  cases horizontal
  · rintro x ⟨hx, hy⟩
    exact ⟨hx ▸ hzero, hI hy⟩
  · rintro x ⟨hx, hy⟩
    exact ⟨hI hx, hy ▸ hzero⟩

end RectangleCornerArcs

namespace Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem disjoint_source_and_target_axis_intervals
    (ψ : Bool → (ℝ × ℝ) → E) (e : Bool → E ≃L[ℝ] F)
    (r : Bool → ℝ) (hr : ∀ j, 0 ≤ r j)
    (U : Bool → Set E) (V : Bool → Set F)
    (hU : Disjoint (U false) (U true)) (hV : Disjoint (V false) (V true))
    (hsource : ∀ j, ψ j '' base (r j) ⊆ U j)
    (htarget : ∀ j, e j '' (ψ j '' base (r j)) ⊆ V j)
    (k l : Bool) {a b : ℝ} (ha : |a| ≤ r false) (hb : |b| ≤ r true) :
    Disjoint (ψ false '' axisInterval k a) (ψ true '' axisInterval l b) ∧
      Disjoint (e false '' (ψ false '' axisInterval k a))
        (e true '' (ψ true '' axisInterval l b)) := by
  have hfalse : ψ false '' axisInterval k a ⊆ ψ false '' base (r false) :=
    image_mono (axisInterval_subset_base k (hr false) ha)
  have htrue : ψ true '' axisInterval l b ⊆ ψ true '' base (r true) :=
    image_mono (axisInterval_subset_base l (hr true) hb)
  exact ⟨hU.mono (hfalse.trans (hsource false)) (htrue.trans (hsource true)),
    hV.mono ((image_mono hfalse).trans (htarget false))
      ((image_mono htrue).trans (htarget true))⟩

end Geometry
