import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Connected.Clopen









namespace Poincare

open Filter Set
open scoped ENNReal NNReal

universe u

variable {X : Type u}



theorem edist_ne_top_of_preconnected [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ∞ := by
  have hclopen : IsClopen (Metric.eball y ∞) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have huniv : Metric.eball y ∞ = univ :=
    hclopen.eq_univ ⟨y, Metric.mem_eball_self ENNReal.coe_lt_top⟩
  have hx : x ∈ Metric.eball y ∞ := by rw [huniv]; trivial
  exact hx.ne




theorem completeSpace_of_local_metric_comparison
    (d₀ d₁ : PseudoMetricSpace X) (x₀ : X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hbounded : ∀ R : ℝ, ∃ S : ℝ, ∀ x : X,
      d₁.dist x x₀ ≤ R → d₀.dist x x₀ ≤ S)
    (hcompare : ∀ R : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x y : X,
      d₀.dist x x₀ ≤ R → d₀.dist y x₀ ≤ R →
      d₁.dist x y ≤ C * d₀.dist x y ∧ d₀.dist x y ≤ C * d₁.dist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  let : PseudoMetricSpace X := d₁
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  rcases cauchySeq_bdd hu with ⟨R, _, huR⟩
  obtain ⟨S, hS⟩ := hbounded (R + d₁.dist (u 0) x₀)
  have huS : ∀ n, d₀.dist (u n) x₀ ≤ S := by
    intro n
    apply hS
    exact (dist_triangle (u n) (u 0) x₀).trans
      (add_le_add (huR n 0).le le_rfl)
  have hucauchy := Metric.cauchySeq_iff.mp hu
  have hlimit : ∃ x, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d₀.dist (u n) x < ε := by
    let : PseudoMetricSpace X := d₀
    let : CompleteSpace X := hcomplete
    have hu₀ : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨C, hC, hcmp⟩ := hcompare S
      obtain ⟨N, hN⟩ := hucauchy (ε / C) (div_pos hε hC)
      refine ⟨N, fun m hm n hn => ?_⟩
      apply lt_of_le_of_lt ((hcmp _ _ (huS m) (huS n)).2)
      simpa [mul_comm] using (lt_div_iff₀ hC).mp (hN m hm n hn)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hu₀
    exact ⟨x, Metric.tendsto_atTop.mp hx⟩
  obtain ⟨x, hx⟩ := hlimit
  refine ⟨x, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨C, hC, hcmp⟩ := hcompare (max S (d₀.dist x x₀))
  obtain ⟨N, hN⟩ := hx (ε / C) (div_pos hε hC)
  refine ⟨N, fun n hn => ?_⟩
  apply lt_of_le_of_lt ((hcmp _ _ ((huS n).trans (le_max_left _ _))
    (le_max_right _ _)).1)
  simpa [mul_comm] using (lt_div_iff₀ hC).mp (hN n hn)




theorem completeSpace_of_local_emetric_comparison
    (d₀ d₁ : PseudoEMetricSpace X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hbounded : ∀ x₀ : X, ∀ R : ℝ≥0, ∃ S : ℝ≥0, ∀ x : X,
      d₁.edist x x₀ ≤ R → d₀.edist x x₀ ≤ S)
    (hcompare : ∀ x₀ : X, ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₀.edist x x₀ ≤ R → d₀.edist y x₀ ≤ R →
      d₁.edist x y ≤ C * d₀.edist x y ∧ d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  let : PseudoEMetricSpace X := d₁
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N₀, hN₀⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  obtain ⟨S, hS⟩ := hbounded (u N₀) 1
  have huS : ∀ n ≥ N₀, d₀.edist (u n) (u N₀) ≤ S :=
    fun n hn => hS _ (hN₀ n hn).le
  have hucauchy := EMetric.cauchySeq_iff.mp hu
  have hlimit : ∃ x, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d₀.edist (u n) x < ε := by
    let : PseudoEMetricSpace X := d₀
    let : CompleteSpace X := hcomplete
    have hu₀ : CauchySeq u := by
      rw [EMetric.cauchySeq_iff]
      intro ε hε
      obtain ⟨C, hcmp⟩ := hcompare (u N₀) S
      obtain ⟨N, hN⟩ := hucauchy (ε / C) (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
      refine ⟨max N₀ N, fun m hm n hn => ?_⟩
      apply lt_of_le_of_lt ((hcmp _ _ (huS m ((le_max_left _ _).trans hm))
        (huS n ((le_max_left _ _).trans hn))).2)
      exact ENNReal.mul_lt_of_lt_div' (hN m ((le_max_right _ _).trans hm)
        n ((le_max_right _ _).trans hn))
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hu₀
    exact ⟨x, EMetric.tendsto_atTop.mp hx⟩
  obtain ⟨x, hx⟩ := hlimit
  obtain ⟨C, hcmp⟩ := hcompare x 1
  obtain ⟨N₁, hN₁⟩ := hx 1 zero_lt_one
  refine ⟨x, EMetric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx (ε / C) (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
  refine ⟨max N₁ N, fun n hn => ?_⟩
  apply lt_of_le_of_lt ((hcmp _ _ (hN₁ n ((le_max_left _ _).trans hn)).le
    (by simp [d₀.edist_self])).1)
  exact ENNReal.mul_lt_of_lt_div' (hN n ((le_max_right _ _).trans hn))



theorem completeSpace_of_local_emetric_comparison_at_basepoint
    (d₀ d₁ : PseudoEMetricSpace X) (x₀ : X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hfinite : ∀ x : X, d₁.edist x x₀ ≠ ∞)
    (hbounded : ∀ R : ℝ≥0, ∃ S : ℝ≥0, ∀ x : X,
      d₁.edist x x₀ ≤ R → d₀.edist x x₀ ≤ S)
    (hcompare : ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₀.edist x x₀ ≤ R → d₀.edist y x₀ ≤ R →
      d₁.edist x y ≤ C * d₀.edist x y ∧ d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  have hfinite₀ : ∀ x : X, d₀.edist x x₀ ≠ ∞ := by
    intro x
    obtain ⟨S, hS⟩ := hbounded (d₁.edist x x₀).toNNReal
    apply ne_top_of_le_ne_top ENNReal.coe_ne_top (hS x _)
    exact (ENNReal.coe_toNNReal (hfinite x)).ge
  apply completeSpace_of_local_emetric_comparison d₀ d₁ hcomplete
  · intro y R
    obtain ⟨S, hS⟩ := hbounded (R + (d₁.edist y x₀).toNNReal)
    refine ⟨S + (d₀.edist y x₀).toNNReal, fun x hx => ?_⟩
    have hx₀ : d₀.edist x x₀ ≤ S := by
      apply hS
      simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (hfinite y)] using
        (d₁.edist_triangle x y x₀).trans (add_le_add hx le_rfl)
    simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (hfinite₀ y),
      d₀.edist_comm x₀ y] using
      (d₀.edist_triangle x x₀ y).trans (add_le_add hx₀ le_rfl)
  · intro y R
    obtain ⟨C, hC⟩ := hcompare (R + (d₀.edist y x₀).toNNReal)
    refine ⟨C, fun x z hx hz => hC x z ?_ ?_⟩
    · simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (hfinite₀ y)] using
        (d₀.edist_triangle x y x₀).trans (add_le_add hx le_rfl)
    · simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (hfinite₀ y)] using
        (d₀.edist_triangle z y x₀).trans (add_le_add hz le_rfl)



theorem completeSpace_of_preconnected_local_emetric_comparison
    (d₀ d₁ : PseudoEMetricSpace X) (x₀ : X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hconnected : @PreconnectedSpace X d₁.toUniformSpace.toTopologicalSpace)
    (hbounded : ∀ R : ℝ≥0, ∃ S : ℝ≥0, ∀ x : X,
      d₁.edist x x₀ ≤ R → d₀.edist x x₀ ≤ S)
    (hcompare : ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₀.edist x x₀ ≤ R → d₀.edist y x₀ ≤ R →
      d₁.edist x y ≤ C * d₀.edist x y ∧ d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  apply completeSpace_of_local_emetric_comparison_at_basepoint d₀ d₁ x₀
    hcomplete ?_ hbounded hcompare
  let : PseudoEMetricSpace X := d₁
  let : PreconnectedSpace X := hconnected
  exact fun x => edist_ne_top_of_preconnected x x₀











theorem completeSpace_family_of_preconnected_local_emetric_comparison
    {ι : Type*} (d₀ : PseudoEMetricSpace X) (d₁ : ι → PseudoEMetricSpace X)
    (x₀ : X) (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hconnected : ∀ i : ι,
      @PreconnectedSpace X (d₁ i).toUniformSpace.toTopologicalSpace)
    (hbounded : ∀ i : ι, ∀ R : ℝ≥0, ∃ S : ℝ≥0, ∀ x : X,
      (d₁ i).edist x x₀ ≤ R → d₀.edist x x₀ ≤ S)
    (hcompare : ∀ i : ι, ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₀.edist x x₀ ≤ R → d₀.edist y x₀ ≤ R →
      (d₁ i).edist x y ≤ C * d₀.edist x y ∧
        d₀.edist x y ≤ C * (d₁ i).edist x y) :
    ∀ i : ι, @CompleteSpace X (d₁ i).toUniformSpace := by
  intro i
  exact completeSpace_of_preconnected_local_emetric_comparison d₀ (d₁ i) x₀
    hcomplete (hconnected i) (hbounded i) (hcompare i)




theorem completeSpace_of_continuous_local_edist_bound
    (d₀ d₁ : PseudoEMetricSpace X) (p : X)
    (hcomplete : @CompleteSpace X d₀.toUniformSpace)
    (hcontinuous : @Continuous X X d₀.toUniformSpace.toTopologicalSpace
      d₁.toUniformSpace.toTopologicalSpace id)
    (hfinite : ∀ x : X, d₁.edist x p ≠ ∞)
    (hcompare : ∀ R : ℝ≥0, ∃ C : ℝ≥0, ∀ x y : X,
      d₁.edist x p ≤ R → d₁.edist y p ≤ R →
      d₀.edist x y ≤ C * d₁.edist x y) :
    @CompleteSpace X d₁.toUniformSpace := by
  let : PseudoEMetricSpace X := d₁
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N₀, hN₀⟩ := EMetric.cauchySeq_iff'.mp hu 1 zero_lt_one
  let R : ℝ≥0 := 1 + (d₁.edist (u N₀) p).toNNReal
  have huR : ∀ n ≥ N₀, d₁.edist (u n) p ≤ R := by
    intro n hn
    calc
      d₁.edist (u n) p ≤ d₁.edist (u n) (u N₀) + d₁.edist (u N₀) p :=
        d₁.edist_triangle _ _ _
      _ ≤ 1 + d₁.edist (u N₀) p := add_le_add (hN₀ n hn).le le_rfl
      _ = R := by simp [R, ENNReal.coe_toNNReal (hfinite (u N₀))]
  obtain ⟨C, hC⟩ := hcompare R
  have hucauchy := EMetric.cauchySeq_iff.mp hu
  have hlimit : ∃ x, Tendsto u atTop
      (@nhds X d₀.toUniformSpace.toTopologicalSpace x) := by
    let : PseudoEMetricSpace X := d₀
    let : CompleteSpace X := hcomplete
    apply cauchySeq_tendsto_of_complete
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hucauchy (ε / C) (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
    refine ⟨max N₀ N, fun m hm n hn ↦ ?_⟩
    apply lt_of_le_of_lt (hC _ _ (huR m ((le_max_left _ _).trans hm))
      (huR n ((le_max_left _ _).trans hn)))
    exact ENNReal.mul_lt_of_lt_div' (hN m ((le_max_right _ _).trans hm)
      n ((le_max_right _ _).trans hn))
  obtain ⟨x, hx⟩ := hlimit
  exact ⟨x, (@Continuous.tendsto X X d₀.toUniformSpace.toTopologicalSpace
    d₁.toUniformSpace.toTopologicalSpace id hcontinuous x).comp hx⟩

end Poincare
