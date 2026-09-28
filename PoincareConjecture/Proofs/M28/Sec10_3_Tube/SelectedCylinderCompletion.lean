import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedNeckVanishingTail
import PoincareConjecture.Proofs.M28.Mathlib.VanishingTailCompletion












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}






theorem exists_unique_selected_cylinder_completion
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (D : LeviCivitaData g) (hR : ContinuousOn D.scalarCurvature T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D.scalarCurvature y ≤ 2 * D.scalarCurvature z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x)
    {B : ℝ} (hB : 0 < B) (hdiam : intrinsicDiameter g (U : Set M) ≤ ENNReal.ofReal B)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∃! E : UniformSpace.Completion U,
      E ∉ Set.range ((↑) : U → UniformSpace.Completion U) ∧
      (∀ eta : ℝ, 0 < eta → ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧
        ∀ x : U, a < (A.inverse x).2 → dist (x : UniformSpace.Completion U) E < eta) ∧
      (∀ q : ℕ → U, Tendsto (fun n => (A.inverse (q n)).2) atTop (𝓝 1) →
        Tendsto (fun n => (q n : UniformSpace.Completion U)) atTop (𝓝 E)) ∧
      Continuous (fun x : U => dist (x : UniformSpace.Completion U) E) ∧
      (∀ x : U, 0 < dist (x : UniformSpace.Completion U) E) ∧
      ∀ x y : U,
        |dist (x : UniformSpace.Completion U) E - dist (y : UniformSpace.Completion U) E| ≤
          dist x y ∧
        dist x y ≤ dist (x : UniformSpace.Completion U) E +
          dist (y : UniformSpace.Completion U) E := by
  let := intrinsicOpenMetricSpace g U hfinite
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hheight : Continuous (fun x : U => (A.inverse x).2) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((continuous_snd.comp_continuousOn A.inverse_smooth.continuousOn).mono hUV)
  have hbelow (x : U) : (A.inverse x).2 < 1 :=
    (A.inverse_mem x (hUV x.property)).2.2
  have hcofinal : ∀ a : ℝ, a < 1 → ∃ x : U, a < (A.inverse x).2 := by
    intro a ha
    have hcpos : 0 < max a (3 / 4 : ℝ) := lt_max_of_lt_right (by norm_num)
    have hc1 : max a (3 / 4 : ℝ) < 1 := max_lt ha (by norm_num)
    obtain ⟨x, hx⟩ := A.tail_nonempty true hcpos hc1
    have hxread := (A.mem_tail_iff_m28 true hcpos hc1).mp hx
    have hxU : x ∈ U := by
      change x ∈ (U : Set M)
      rw [hU]
      exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
        ⟨hxread.1, lt_trans (by norm_num : (1 / 2 : ℝ) < 3 / 4)
          ((le_max_right _ _).trans_lt hxread.2)⟩
    exact ⟨⟨x, hxU⟩, (le_max_left _ _).trans_lt hxread.2⟩
  obtain ⟨p, _hp⟩ := hcofinal 0 (by norm_num)
  have hshrink : ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, a < 1 ∧
      ∀ x y : U, a < (A.inverse x).2 → a < (A.inverse y).2 → dist x y < eta := by
    intro eta heta
    obtain ⟨a, _ha, ha1, hclose⟩ := exists_vanishing_selected_cylinder_tail
      T A U hU hA D hR hratio hdiverge hB hdiam p eta heta
    refine ⟨a, ha1, ?_⟩
    intro x y hx hy
    have hxy := hclose x y hx hy
    rw [← intrinsicOpenMetricSpace_edist g U hfinite x y, edist_dist] at hxy
    exact (ENNReal.ofReal_lt_ofReal_iff heta).mp hxy
  obtain ⟨E, ⟨houtside, htail, hsequences, hcontinuous, hpositive, htriangle⟩, hunique⟩ :=
    UniformSpace.Completion.exists_unique_of_vanishing_height_tails
      (fun x : U => (A.inverse x).2) hheight hbelow hcofinal hshrink
  refine ⟨E, ⟨houtside, ?_, hsequences, hcontinuous, hpositive, htriangle⟩, ?_⟩
  · intro eta heta
    obtain ⟨a, ha1, hclose⟩ := htail eta heta
    refine ⟨max a (3 / 4 : ℝ), lt_max_of_lt_right (by norm_num),
      max_lt ha1 (by norm_num), ?_⟩
    intro x hx
    exact hclose x ((le_max_left _ _).trans_lt hx)
  · intro F hF
    apply hunique F
    refine ⟨hF.1, ?_, hF.2.2⟩
    intro eta heta
    obtain ⟨a, _ha, ha1, hclose⟩ := hF.2.1 eta heta
    exact ⟨a, ha1, hclose⟩

end PoincareConjecture.M28
