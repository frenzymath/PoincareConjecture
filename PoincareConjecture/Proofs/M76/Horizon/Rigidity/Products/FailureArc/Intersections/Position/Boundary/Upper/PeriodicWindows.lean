import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Translations.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PeriodicSquare

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem exists_small_translation_periodic_window_charts
    {p : ℝ} [Fact (0 < p)] {I J : Type*} [Finite I] [Finite J]
    (a b : I → P2) (c d : J → P2) (hcd : ∀ j, c j ≠ d j)
    (hselfA : ∀ i k, i ≠ k →
      segment ℝ (a i) (b i) ∩ segment ℝ (a k) (b k) ⊆ {a i, b i})
    (hselfB : ∀ j k, j ≠ k →
      segment ℝ (c j) (d j) ∩ segment ℝ (c k) (d k) ⊆ {c j, d j})
    (C₀ C₁ : Set (AddCircle p × AddCircle p))
    (hwindow₀ : ∀ z ∈ Icc (-p) (2 * p) ×ˢ Icc (-p) (2 * p),
      ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈ C₀ ↔
        z ∈ ⋃ i, segment ℝ (a i) (b i))
    (hwindow₁ : ∀ z ∈ Icc (-p) (2 * p) ×ˢ Icc (-p) (2 * p),
      ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈ C₁ ↔
        z ∈ ⋃ j, segment ℝ (c j) (d j)) :
    ∃ v : P2, ‖v‖ < p / 4 ∧
      (C₀ ∩ (fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁).Finite ∧
      ∀ q ∈ C₀ ∩ (fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁,
        ∃ (A : P2 ≃ᴬ[ℝ] P2) (U : Set P2),
          IsOpen U ∧ A 0 ∈ U ∧ (((A 0).1 : AddCircle p), ((A 0).2 : AddCircle p)) = q ∧
          (∀ z, A z ∈ U →
            ((((A z).1 : AddCircle p), ((A z).2 : AddCircle p)) ∈ C₀ ↔ z.2 = 0)) ∧
          ∀ z, A z ∈ U →
            ((((A z).1 : AddCircle p), ((A z).2 : AddCircle p)) ∈
              (fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁ ↔ z.1 = 0) := by
  have hp : 0 < p := Fact.out
  let π (z : P2) := ((z.1 : AddCircle p), (z.2 : AddCircle p))
  let W : Set P2 := Ioo (-p) (2 * p) ×ˢ Ioo (-p) (2 * p)
  obtain ⟨v, hv, hfinite, hcharts⟩ :=
    UpperTranslation.exists_small_translation_whole_family_charts a b c d hcd
      hselfA hselfB (show 0 < p / 4 by positivity)
  have htranslate (z : P2) :
      z ∈ (⋃ j, segment ℝ (c j + v) (d j + v)) ↔
        z - v ∈ ⋃ j, segment ℝ (c j) (d j) := by
    simp only [mem_iUnion]
    apply exists_congr
    intro j
    have hzv : v + (z - v) = z := by abel
    simpa only [hzv, add_comm v (c j), add_comm v (d j)] using
      (mem_segment_translate ℝ v (x := z - v) (b := c j) (c := d j))
  have hπtranslate (z : P2) : π z ∈ (fun q => q + π v) '' C₁ ↔ π (z - v) ∈ C₁ := by
    have hsub : π (z - v) = π z - π v := by
      simp only [π, AddCircle.coe_sub, Prod.sub_def]
    rw [hsub]
    constructor
    · rintro ⟨q, hq, heq⟩
      rwa [(sub_eq_iff_eq_add.mpr heq.symm : π z - π v = q)]
    · intro hz
      exact ⟨π z - π v, hz, sub_add_cancel _ _⟩
  have hWclosed : W ⊆ Icc (-p) (2 * p) ×ˢ Icc (-p) (2 * p) := by
    intro z hz
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hwindowv (z : P2) (hz : z - v ∈ W) :
      π z ∈ (fun q => q + π v) '' C₁ ↔ z ∈ ⋃ j, segment ℝ (c j + v) (d j + v) := by
    rw [hπtranslate, hwindow₁ _ (hWclosed hz), htranslate]
  have hrep (q : AddCircle p × AddCircle p) :
      ∃ z : P2, π z = q ∧ z ∈ W ∧ z - v ∈ W := by
    obtain ⟨w, hw⟩ := surjective_projection p q
    let z : P2 := (w.1, w.2)
    have hx := w.1.property
    have hy := w.2.property
    have hvx : |v.1| < p / 4 := (show |v.1| ≤ ‖v‖ by
      simpa only [Real.norm_eq_abs] using norm_fst_le v).trans_lt hv
    have hvy : |v.2| < p / 4 := (show |v.2| ≤ ‖v‖ by
      simpa only [Real.norm_eq_abs] using norm_snd_le v).trans_lt hv
    refine ⟨z, hw, ?_, ?_⟩
    · change (-p < (w.1 : ℝ) ∧ (w.1 : ℝ) < 2 * p) ∧
        (-p < (w.2 : ℝ) ∧ (w.2 : ℝ) < 2 * p)
      constructor <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    · change (-p < (w.1 : ℝ) - v.1 ∧ (w.1 : ℝ) - v.1 < 2 * p) ∧
        (-p < (w.2 : ℝ) - v.2 ∧ (w.2 : ℝ) - v.2 < 2 * p)
      have hvx' := abs_lt.mp hvx
      have hvy' := abs_lt.mp hvy
      constructor <;> constructor <;>
        linarith [hx.1, hx.2, hy.1, hy.2, hvx'.1, hvx'.2, hvy'.1, hvy'.2]
  refine ⟨v, hv, ?_, ?_⟩
  · apply (hfinite.image π).subset
    intro q hq
    obtain ⟨z, hzq, hzW, hzvW⟩ := hrep q
    refine ⟨z, ⟨?_, ?_⟩, hzq⟩
    · exact (hwindow₀ z (hWclosed hzW)).mp (show π z ∈ C₀ from hzq.symm ▸ hq.1)
    · exact (hwindowv z hzvW).mp (hzq.symm ▸ hq.2)
  · intro q hq
    obtain ⟨z, hzq, hzW, hzvW⟩ := hrep q
    have hzleft := (hwindow₀ z (hWclosed hzW)).mp
      (show π z ∈ C₀ from hzq.symm ▸ hq.1)
    have hzright := (hwindowv z hzvW).mp (hzq.symm ▸ hq.2)
    let O := W ∩ (fun z : P2 => z - v) ⁻¹' W
    have hW : IsOpen W := isOpen_Ioo.prod isOpen_Ioo
    have hO : IsOpen O := hW.inter (hW.preimage (continuous_id.sub continuous_const))
    obtain ⟨A, U, hU, hzU, hUO, hA0, haxis₀, haxis₁⟩ :=
      hcharts z ⟨hzleft, hzright⟩ O hO ⟨hzW, hzvW⟩
    refine ⟨A, U, hU, hA0.symm ▸ hzU, ?_, ?_, ?_⟩
    · change π (A 0) = q
      rwa [hA0]
    · intro w hw
      exact (hwindow₀ (A w) (hWclosed (hUO hw).1)).trans (haxis₀ w hw)
    · intro w hw
      exact (hwindowv (A w) (hUO hw).2).trans (haxis₁ w hw)

end PoincareConjecture.M76.PeriodicSquare
