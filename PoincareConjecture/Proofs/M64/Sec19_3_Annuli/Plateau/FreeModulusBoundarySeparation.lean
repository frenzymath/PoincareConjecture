import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakVerticalSeparation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64




theorem periodic_curves_observed_separation
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (e : X → E) (he : Continuous e) (hinj : Function.Injective e)
    {c0 c1 : ℝ → X} (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (hdisjoint : Disjoint (range c0) (range c1)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x y : ℝ, delta ≤ ‖e (c1 y) - e (c0 x)‖ ^ 2 := by
  let D := fun z : ℝ × ℝ => ‖e (c1 z.2) - e (c0 z.1)‖ ^ 2
  have hD1 : Continuous (fun z : ℝ × ℝ => e (c1 z.2)) :=
    (he.comp hc1).comp continuous_snd
  have hD0 : Continuous (fun z : ℝ × ℝ => e (c0 z.1)) :=
    (he.comp hc0).comp continuous_fst
  have hD : Continuous D := (hD1.sub hD0).norm.pow 2
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hne : (Icc (0 : ℝ) curvePeriod ×ˢ Icc (0 : ℝ) curvePeriod).Nonempty :=
    ⟨(0, 0), ⟨le_rfl, hP.le⟩, ⟨le_rfl, hP.le⟩⟩
  have hK : IsCompact (Icc (0 : ℝ) curvePeriod ×ˢ Icc (0 : ℝ) curvePeriod) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨z, -, hz⟩ := hK.exists_isMinOn hne hD.continuousOn
  have hneq : e (c1 z.2) - e (c0 z.1) ≠ 0 := by
    intro h
    have hh := hinj (sub_eq_zero.mp h)
    exact Set.disjoint_left.mp hdisjoint
      (show c0 z.1 ∈ range c0 from mem_range_self z.1)
      (show c0 z.1 ∈ range c1 from ⟨z.2, hh⟩)
  refine ⟨D z, sq_pos_of_pos (norm_pos_iff.mpr hneq), ?_⟩
  intro x y
  obtain ⟨x', hx', hxx⟩ := hp0.exists_mem_Ico₀ hP x
  obtain ⟨y', hy', hyy⟩ := hp1.exists_mem_Ico₀ hP y
  rw [hxx, hyy]
  exact hz (show (x', y') ∈ Icc (0 : ℝ) curvePeriod ×ˢ Icc (0 : ℝ) curvePeriod from
    ⟨Ico_subset_Icc_self hx', Ico_subset_Icc_self hy'⟩)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]



theorem free_annulus_inverse_modulus_bound_of_disjoint_images
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (hdisjoint : Disjoint (range c0) (range c1)) :
    ∃ beta : ℝ, 0 < beta ∧
      ∀ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma0.map → ContDiff ℝ 1 sigma1.map →
      ∀ A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
      ∀ r : ℝ, 0 < r → beta * r⁻¹ ≤ m64ClassicalWeightedGramEnergy g A r := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨Q, K, hQ, -, hb, hpos, -, hgram⟩ :=
    m64ChartReadable_observed_metric g e he1 hread
  obtain ⟨C, -, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he1 Q hgram
  obtain ⟨delta, hdelta, hsep⟩ := periodic_curves_observed_separation e he.continuous
    hei.injective hc0.continuous hc1.continuous hp0 hp1 hdisjoint
  have hC : 0 < max C 1 := lt_max_of_lt_right zero_lt_one
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let beta := curvePeriod * delta / (2 * max C 1)
  refine ⟨beta, div_pos (mul_pos hP hdelta) (mul_pos (by norm_num) hC), ?_⟩
  intro sigma0 sigma1 hs0 hs1 A r hr
  have hc0e : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he1.comp hc0)
  have hc1e : ContDiff ℝ 1 (e ∘ c1) := contMDiff_iff_contDiff.mp (he1.comp hc1)
  have hd : ContDiff ℝ 1 (fun x => e ((c1 ∘ sigma1.map) x) -
      e ((c0 ∘ sigma0.map) x)) := (hc1e.comp hs1).sub (hc0e.comp hs0)
  obtain ⟨W, hmap, hcol⟩ := m64ObservedWeakAnnulus_of_annulus A e he1
  have hWE := m64ObservedWeakAnnulus_seed_weightedEnergy_eq A e he1 Q
    (m64ObservedMetric_tangent_diagonal g e he1 Q hgram) W hmap hcol r
  have hvertical := W.weightedEnergy_ge_vertical_boundary Q hQ hei.isEmbedding hb
    hpos hcoercive hd hr
  have hint : curvePeriod * delta ≤ ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖e ((c1 ∘ sigma1.map) x) - e ((c0 ∘ sigma0.map) x)‖ ^ 2 := by
    calc
      _ = ∫ _x in Icc (0 : ℝ) curvePeriod, delta := by simp [hP.le]
      _ ≤ _ := by
        apply integral_mono
          (show IntegrableOn (fun _ : ℝ => delta) (Icc (0 : ℝ) curvePeriod) volume from
            integrableOn_const isCompact_Icc.measure_ne_top)
          ((hd.continuous.norm.pow 2).integrableOn_Icc)
        intro x
        exact hsep (sigma0.map x) (sigma1.map x)
  calc
    beta * r⁻¹ = (r⁻¹ / (2 * max C 1)) * (curvePeriod * delta) := by dsimp [beta]; ring
    _ ≤ (r⁻¹ / (2 * max C 1)) * ∫ x in Icc (0 : ℝ) curvePeriod,
        ‖e ((c1 ∘ sigma1.map) x) - e ((c0 ∘ sigma0.map) x)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ W.weightedEnergy Q r := hvertical
    _ = m64ClassicalWeightedGramEnergy g A r := hWE

end PoincareConjecture.M64
