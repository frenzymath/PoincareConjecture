import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.RadialAffineArea












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture

private theorem m64_radial_line_null (c : ℝ) :
    volume {p : LoopPlane | p 1 = c} = 0 := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let q : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp _
  have hq : MeasurePreserving q volume volume :=
    MeasureTheory.volume_preserving_finTwoArrow ℝ
  have hcomp : MeasurePreserving (q ∘ e) volume volume := hq.comp he
  let S : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ {c}
  have hS : NullMeasurableSet S volume := by measurability
  have hzero : volume S = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  have hpre := hcomp.measure_preimage hS
  have heq : (q ∘ e) ⁻¹' S = {p : LoopPlane | p 1 = c} := by
    ext p
    simp [q, e, S, MeasurableEquiv.finTwoArrow_apply]
  rw [← heq, hpre, hzero]

private def lowerHalf : Set LoopPlane :=
  m64AnnulusDomain ∩ {p | p 1 ≤ (1 / 2 : ℝ)}

private def upperHalf : Set LoopPlane :=
  m64AnnulusDomain ∩ {p | (1 / 2 : ℝ) ≤ p 1}

private theorem lowerHalf_image :
    m64RadialAffine 2 0 '' lowerHalf = m64AnnulusDomain := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change 0 ≤ q 0 ∧ q 0 ≤ curvePeriod ∧ 0 ≤ 2 * q 1 + 0 ∧ 2 * q 1 + 0 ≤ 1
    have hhalf : q 1 ≤ (1 / 2 : ℝ) := hq.2
    exact ⟨hq.1.1, hq.1.2.1, by linarith [hq.1.2.2.1], by linarith⟩
  · intro hp
    refine ⟨annulusPoint (p 0) (p 1 / 2), ?_, ?_⟩
    · change (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 / 2 ∧ p 1 / 2 ≤ 1) ∧
        p 1 / 2 ≤ 1 / 2
      exact ⟨⟨hp.1, hp.2.1, by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩,
        by linarith [hp.2.2.2]⟩
    · ext i
      fin_cases i <;> simp [m64RadialAffine, annulusPoint]
      ring

private theorem upperHalf_image :
    m64RadialAffine 2 (-1) '' upperHalf = m64AnnulusDomain := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change 0 ≤ q 0 ∧ q 0 ≤ curvePeriod ∧ 0 ≤ 2 * q 1 + -1 ∧ 2 * q 1 + -1 ≤ 1
    have hhalf : (1 / 2 : ℝ) ≤ q 1 := hq.2
    exact ⟨hq.1.1, hq.1.2.1, by linarith, by linarith [hq.1.2.2.2]⟩
  · intro hp
    refine ⟨annulusPoint (p 0) ((p 1 + 1) / 2), ?_, ?_⟩
    · change (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ (p 1 + 1) / 2 ∧
        (p 1 + 1) / 2 ≤ 1) ∧ 1 / 2 ≤ (p 1 + 1) / 2
      exact ⟨⟨hp.1, hp.2.1, by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩,
        by linarith [hp.2.2.1]⟩
    · ext i
      fin_cases i <;> simp [m64RadialAffine, annulusPoint]
      ring

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in


theorem m64AnnulusJoin_area {g : RiemannianMetric n M} {c0 c1 c2 : ℝ → M}
    (A : M64Annulus g c0 c1) (B : M64Annulus g c1 c2)
    (C : M64Annulus g c0 c2) (hmap : C.map = m64AnnulusJoinMap A.map B.map) :
    C.area = A.area + B.area := by
  have hleft : MeasurableSet lowerHalf := m64AnnulusDomain_measurableSet.inter
    (measurableSet_le (by fun_prop) measurable_const)
  have hright : MeasurableSet upperHalf := m64AnnulusDomain_measurableSet.inter
    (measurableSet_le measurable_const (by fun_prop))
  have hline : ∀ᵐ p ∂(volume : Measure LoopPlane), p 1 ≠ (1 / 2 : ℝ) :=
    compl_mem_ae_iff.mpr (m64_radial_line_null _)
  have hleftDensity : ∀ᵐ p ∂volume.restrict lowerHalf,
      m60AreaDensity g C.map p =
        m60AreaDensity g (A.map ∘ m64RadialAffine 2 0) p := by
    filter_upwards [hline.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem hleft] with p hp hpd
    have hlt : p 1 < (1 / 2 : ℝ) := lt_of_le_of_ne hpd.2 hp
    apply m60AreaDensity_congr_of_eventuallyEq g
    filter_upwards [(isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
      continuous_const).mem_nhds hlt] with q hq
    rw [hmap]
    simp only [m64AnnulusJoinMap, if_pos hq.le, Function.comp_def]
    congr 1
    ext i
    fin_cases i <;> simp [m64RadialDouble, m64RadialAffine, annulusPoint]
  have hrightDensity : ∀ᵐ p ∂volume.restrict upperHalf,
      m60AreaDensity g C.map p =
        m60AreaDensity g (B.map ∘ m64RadialAffine 2 (-1)) p := by
    filter_upwards [hline.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem hright] with p hp hpd
    have hlt : (1 / 2 : ℝ) < p 1 := lt_of_le_of_ne hpd.2 (Ne.symm hp)
    apply m60AreaDensity_congr_of_eventuallyEq g
    filter_upwards [(isOpen_lt continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).mem_nhds hlt] with q hq
    rw [hmap]
    simp only [m64AnnulusJoinMap, if_neg (not_le_of_gt hq), Function.comp_def]
    congr 1
  have hleftArea : (∫ p in lowerHalf, m60AreaDensity g C.map p) = A.area := by
    rw [integral_congr_ae hleftDensity,
      m64AreaIntegral_comp_radialAffine g A.map (by norm_num) 0 hleft, lowerHalf_image]
    rfl
  have hrightArea : (∫ p in upperHalf, m60AreaDensity g C.map p) = B.area := by
    rw [integral_congr_ae hrightDensity,
      m64AreaIntegral_comp_radialAffine g B.map (by norm_num) (-1) hright, upperHalf_image]
    rfl
  have hunion : lowerHalf ∪ upperHalf = m64AnnulusDomain := by
    ext p
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp
      rcases le_total (p 1) (1 / 2 : ℝ) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
  have hdis : AEDisjoint volume lowerHalf upperHalf := by
    apply measure_mono_null ?_ (m64_radial_line_null (1 / 2))
    intro p hp
    exact le_antisymm hp.1.2 hp.2.2
  change (∫ p in m64AnnulusDomain, m60AreaDensity g C.map p) = _
  rw [← hunion, setIntegral_union₀ hdis hright.nullMeasurableSet
    (C.area_integrable.mono_set inter_subset_left)
    (C.area_integrable.mono_set inter_subset_left), hleftArea, hrightArea]



theorem m64Annulus_join_with_area
    {g : RiemannianMetric n M} {c0 c1 c2 : ℝ → M}
    (A : M64Annulus g c0 c1) (B : M64Annulus g c1 c2) :
    ∃ C : M64Annulus g c0 c2,
      C.map = m64AnnulusJoinMap A.map B.map ∧ C.area = A.area + B.area := by
  obtain ⟨C, hmap⟩ := m64Annulus_join A B
  exact ⟨C, hmap, m64AnnulusJoin_area A B C hmap⟩

end PoincareConjecture
