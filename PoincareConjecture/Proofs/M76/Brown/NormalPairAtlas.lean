import PoincareConjecture.Proofs.M76.Brown.NormalTransitionSigns
import PoincareConjecture.Proofs.M76.Brown.NormalChartTransitions









set_option autoImplicit false

open Set SignType

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X]




structure FlatteningAtlas (P : Type*) [TopologicalSpace P] (S : Set X) (ι : Type*) where
  chart : ι → OpenPartialHomeomorph X (P × ℝ)
  pair : ∀ i y, y ∈ (chart i).source → (y ∈ S ↔ (chart i y).2 = 0)
  indexAt : S → ι
  mem_source_at : ∀ x : S, (x : X) ∈ (chart (indexAt x)).source

namespace FlatteningAtlas

variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {S : Set X}
  (A : FlatteningAtlas P S ι)

def baseSet (i : ι) : Set S := (Subtype.val : S → X) ⁻¹' (A.chart i).source

omit [NormedSpace ℝ P] in
theorem isOpen_baseSet (i : ι) : IsOpen (A.baseSet i) :=
  (A.chart i).open_source.preimage continuous_subtype_val

def coordinate (i : ι) (x : S) : P := (A.chart i (x : X)).1

omit [NormedSpace ℝ P] in
theorem base_coordinate (i : ι) (x : S) (hx : x ∈ A.baseSet i) :
    (A.coordinate i x, (0 : ℝ)) = A.chart i (x : X) := by
  apply Prod.ext
  · rfl
  · exact ((A.pair i x hx).mp x.property).symm

def transition (i j : ι) : OpenPartialHomeomorph (P × ℝ) (P × ℝ) :=
  (A.chart i).symm.trans (A.chart j)

omit [NormedSpace ℝ P] in
theorem transition_pair (i j : ι) :
    ∀ z ∈ (A.transition i j).source, (A.transition i j z).2 = 0 ↔ z.2 = 0 := by
  intro z hz
  change (A.chart j ((A.chart i).symm z)).2 = 0 ↔ z.2 = 0
  calc
    _ ↔ (A.chart i).symm z ∈ S := (A.pair j _ hz.2).symm
    _ ↔ (A.chart i ((A.chart i).symm z)).2 = 0 :=
      A.pair i _ ((A.chart i).map_target hz.1)
    _ ↔ z.2 = 0 := by rw [(A.chart i).right_inv hz.1]

omit [NormedSpace ℝ P] in
theorem transition_mem_source (i j : ι) (x : S)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    (A.coordinate i x, (0 : ℝ)) ∈ (A.transition i j).source := by
  refine ⟨?_, ?_⟩
  · change (A.coordinate i x, (0 : ℝ)) ∈ (A.chart i).target
    rw [A.base_coordinate i x hx.1]
    exact (A.chart i).map_source hx.1
  · change (A.chart i).symm (A.coordinate i x, 0) ∈ (A.chart j).source
    rw [A.base_coordinate i x hx.1, (A.chart i).left_inv hx.1]
    exact hx.2

omit [NormedSpace ℝ P] in
theorem transition_base (i j : ι) (x : S)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    A.transition i j (A.coordinate i x, 0) = (A.coordinate j x, 0) := by
  change A.chart j ((A.chart i).symm (A.coordinate i x, 0)) = (A.coordinate j x, 0)
  rw [A.base_coordinate i x hx.1, (A.chart i).left_inv hx.1]
  exact (A.base_coordinate j x hx.2).symm



noncomputable def transitionSign (i j : ι) (x : S) : SignType := by
  classical
  exact if h : x ∈ A.baseSet i ∩ A.baseSet j then
    normalTransitionSign (A.transition i j) (A.transition_pair i j)
      ⟨A.coordinate i x, A.transition_mem_source i j x h⟩
  else 1

theorem transitionSign_spec (i j : ι) (x : S)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    NormalSignAt (A.transition i j) (A.coordinate i x) (A.transitionSign i j x) := by
  rw [transitionSign, dif_pos hx]
  exact normalTransitionSign_spec _ _ _

theorem transitionSign_ne_zero (i j : ι) (x : S) : A.transitionSign i j x ≠ 0 := by
  classical
  by_cases hx : x ∈ A.baseSet i ∩ A.baseSet j
  · exact (A.transitionSign_spec i j x hx).1
  · rw [transitionSign, dif_neg hx]
    exact one_ne_zero

theorem transitionSign_self (i : ι) (x : S) (hx : x ∈ A.baseSet i) :
    A.transitionSign i i x = 1 := by
  apply (A.transitionSign_spec i i x ⟨hx, hx⟩).unique
  refine ⟨one_ne_zero, (A.transition i i).source, (A.transition i i).open_source,
    A.transition_mem_source i i x ⟨hx, hx⟩, subset_rfl, ?_⟩
  intro z hz
  change sign (A.chart i ((A.chart i).symm z)).2 = 1 * sign z.2
  rw [(A.chart i).right_inv hz.1, one_mul]

theorem transitionSign_cocycle (i j k : ι) (x : S)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j ∩ A.baseSet k) :
    A.transitionSign j k x * A.transitionSign i j x = A.transitionSign i k x := by
  exact normal_chart_sign_cocycle (A.chart i) (A.chart j) (A.chart k) x hx.1.1
    ((A.pair i x hx.1.1).mp x.property)
    (A.transitionSign_spec i j x hx.1)
    (A.transitionSign_spec j k x ⟨hx.1.2, hx.2⟩)
    (A.transitionSign_spec i k x ⟨hx.1.1, hx.2⟩)




theorem continuousOn_transitionSign (i j : ι) :
    ContinuousOn (A.transitionSign i j) (A.baseSet i ∩ A.baseSet j) := by
  let f : ↥(A.baseSet i ∩ A.baseSet j) →
      {p : P // (p, (0 : ℝ)) ∈ (A.transition i j).source} :=
    fun x => ⟨A.coordinate i x.val, A.transition_mem_source i j x.val x.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact ((A.chart i).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.property.1)).fst
  have hc := (normalTransitionSign_isLocallyConstant
    (A.transition i j) (A.transition_pair i j)).continuous.comp hf
  rw [continuousOn_iff_continuous_domRestrict]
  convert hc using 1
  funext x
  exact dif_pos x.property

end FlatteningAtlas

end BrownCollar
