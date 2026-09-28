import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckExcursionSubarcs
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckAxialLength
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphSides
import PoincareConjecture.Proofs.M28.Mathlib.PathLengthAnchors













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem exists_two_contained_collar_levels (W : EpsilonNeck g)
    {r : ℝ} (hr : 0 < r) (hrA : r < W.epsilon⁻¹)
    {γ : ℝ → M} {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hγ : ContinuousOn γ (Icc a b)) (hcenter : γ t = W.center)
    (haout : γ a ∉ W.carrier) (hbout : γ b ∉ W.carrier) :
    ∃ c ∈ Ioo a t, ∃ d ∈ Ioo t b, MapsTo γ (Icc c d) W.carrier ∧
      |(W.coordinate_inverse (γ c)).2| = r ∧
      |(W.coordinate_inverse (γ d)).2| = r := by
  have htcenter : γ t ∈ W.central_sphere := by
    rw [hcenter]
    exact W.center_on_central_sphere
  have htzero : (W.coordinate_inverse (γ t)).2 = 0 :=
    (W.mem_central_sphere_iff_of_mem_carrier
      (W.central_sphere_subset htcenter)).mp htcenter
  obtain ⟨d, htd, hdb, hdW, hdlevel⟩ := W.exists_first_neck_collar_subarc hr hrA
    htb.le (hγ.mono (Icc_subset_Icc hat.le le_rfl)) htcenter
    (fun h => hbout h.1)
  have hdb' : d < b := lt_of_le_of_ne hdb (by
    intro heq
    subst d
    exact hbout (hdW (right_mem_Icc.mpr htd.le)))
  let η : ℝ → M := fun s => γ (-s)
  have hneg : MapsTo (fun s : ℝ => -s) (Icc (-t) (-a)) (Icc a b) := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2, htb]
  have hη : ContinuousOn η (Icc (-t) (-a)) :=
    hγ.comp (show Continuous (fun s : ℝ => -s) from continuous_neg).continuousOn hneg
  have hηcenter : η (-t) ∈ W.central_sphere := by
    simpa only [η, neg_neg] using htcenter
  have hηout : η (-a) ∉ W.region (-r) r := by
    intro h
    apply haout
    simpa only [η, neg_neg] using h.1
  obtain ⟨e, hte, hea, heW, helevel⟩ := W.exists_first_neck_collar_subarc hr hrA
    (neg_le_neg hat.le) hη hηcenter hηout
  have hac : a ≤ -e := by linarith only [hea]
  have hct : -e < t := by linarith only [hte]
  have hleft : MapsTo γ (Icc (-e) t) W.carrier := by
    intro s hs
    have hs' : -s ∈ Icc (-t) e := ⟨neg_le_neg hs.2, by linarith only [hs.1]⟩
    simpa only [η, neg_neg] using heW hs'
  have hac' : a < -e := lt_of_le_of_ne hac (by
    intro heq
    apply haout
    rw [heq]
    exact hleft (left_mem_Icc.mpr hct.le))
  refine ⟨-e, ⟨hac', hct⟩, d, ⟨htd, hdb'⟩, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hst : s ≤ t
    · exact hleft ⟨hs.1, hst⟩
    · exact hdW ⟨(lt_of_not_ge hst).le, hs.2⟩
  · simpa only [η, neg_neg, htzero, sub_zero] using helevel
  · simpa only [htzero, sub_zero] using hdlevel

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]




theorem exists_neck_minimizer_opposite_levels (W : EpsilonNeck g)
    (hε : W.epsilon ≤ 1 / 1000) {U : Set M} (hWU : W.carrier ⊆ U)
    {γ : ℝ → M} {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcenter : γ t = W.center)
    (haout : γ a ∉ W.carrier) (hbout : γ b ∉ W.carrier) :
    ∃ c ∈ Ioo a t, ∃ d ∈ Ioo t b, MapsTo γ (Icc c d) W.carrier ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        σ * (W.coordinate_inverse (γ c)).2 = -(9 * W.epsilon⁻¹ / 10) ∧
        σ * (W.coordinate_inverse (γ d)).2 = 9 * W.epsilon⁻¹ / 10 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hApos : 0 < W.epsilon⁻¹ := inv_pos.mpr W.epsilon_pos
  have hA : (1000 : ℝ) ≤ W.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    rw [mul_inv_cancel₀ W.epsilon_pos.ne'] at h
    linarith only [h]
  have hr : 0 < 9 * W.epsilon⁻¹ / 10 := by positivity
  have hrA : 9 * W.epsilon⁻¹ / 10 < W.epsilon⁻¹ := by linarith only [hApos]
  obtain ⟨c, hc, d, hd, hcdW, hcabs, hdabs⟩ :=
    exists_two_contained_collar_levels W hr hrA hat htb hγ.continuousOn
      hcenter haout hbout
  have hfinite : g.pathELength γ a b ≠ ⊤ := by
    rw [pathELength_eq_integral_fixed_segment_speed g hγ le_rfl
      (hat.trans htb).le le_rfl]
    exact ENNReal.ofReal_ne_top
  have hcd : c < d := hc.2.trans hd.1
  have hminimum := pathELength_eq_intrinsicEDist_subsegment g hc.1.le hcd.le hd.2.le
    hγ hγU hfinite hmin
  have hneq : (W.coordinate_inverse (γ c)).2 ≠ (W.coordinate_inverse (γ d)).2 := by
    intro hequal
    have hcW : γ c ∈ W.carrier := hcdW (left_mem_Icc.mpr hcd.le)
    have hdW : γ d ∈ W.carrier := hcdW (right_mem_Icc.mpr hcd.le)
    have hupper := (intrinsicEDist_mono_of_subset (g := g) hWU).trans
      (W.intrinsicEDist_le_axial_add hcW hdW)
    rw [← hequal, sub_self, abs_zero, zero_add] at hupper
    have hroot : Real.sqrt (1 + W.epsilon) ≤ (2 : ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · linarith only [W.epsilon_lt_half]
    have hsqrt2 : Real.sqrt 2 ≤ (2 : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
      calc
        _ ≤ 2 * (Real.pi + 1) :=
          mul_le_mul_of_nonneg_right hsqrt2 (by positivity)
        _ ≤ 10 := by linarith only [Real.pi_le_four]
    have hcoefficient : Real.sqrt (1 + W.epsilon) *
        (Real.sqrt 2 * (Real.pi + 1)) ≤ (20 : ℝ) := by
      have h := mul_le_mul hroot hsphere
        (by positivity : 0 ≤ Real.sqrt 2 * (Real.pi + 1)) (by norm_num)
      norm_num at h
      exact h
    have hscaled : W.scale * Real.sqrt (1 + W.epsilon) *
        (Real.sqrt 2 * (Real.pi + 1)) ≤ 20 * W.scale := by
      have h := mul_le_mul_of_nonneg_left hcoefficient W.scale_pos.le
      nlinarith only [h]
    have hshort : intrinsicEDist g U (γ c) (γ d) ≤ ENNReal.ofReal (20 * W.scale) :=
      hupper.trans (ENNReal.ofReal_le_ofReal hscaled)
    have htzero : (W.coordinate_inverse (γ t)).2 = 0 := by
      rw [hcenter]
      exact (W.mem_central_sphere_iff_of_mem_carrier
        (W.central_sphere_subset W.center_on_central_sphere)).mp W.center_on_central_sphere
    have hcost := path_axial_displacement_le W hc.2.le
      (hγ.mono (Icc_subset_Icc hc.1.le htb.le))
      (fun s hs => hcdW ⟨hs.1, hs.2.trans hd.1.le⟩)
    rw [htzero, zero_sub, abs_neg, hcabs] at hcost
    have hlong : ENNReal.ofReal ((W.scale / 2) * (9 * W.epsilon⁻¹ / 10)) ≤
        g.pathELength γ c d :=
      hcost.trans (Manifold.pathELength_mono le_rfl hd.1.le)
    rw [hminimum] at hlong
    have hgap : 20 * W.scale < (W.scale / 2) * (9 * W.epsilon⁻¹ / 10) := by
      have h : (20 : ℝ) < (1 / 2 : ℝ) * (9 * W.epsilon⁻¹ / 10) := by
        linarith only [hA]
      have hs := mul_lt_mul_of_pos_left h W.scale_pos
      nlinarith only [hs]
    have hpositive : 0 < (W.scale / 2) * (9 * W.epsilon⁻¹ / 10) :=
      mul_pos (div_pos W.scale_pos (by norm_num)) hr
    exact (not_lt_of_ge (hlong.trans hshort))
      ((ENNReal.ofReal_lt_ofReal_iff hpositive).mpr hgap)
  refine ⟨c, hc, d, hd, hcdW, ?_⟩
  rcases (abs_eq hr.le).mp hcabs with hcpos | hcneg
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · simp only [neg_one_mul, hcpos]
    · rcases (abs_eq hr.le).mp hdabs with hdpos | hdneg
      · exact False.elim (hneq (hcpos.trans hdpos.symm))
      · simp only [neg_one_mul, hdneg, neg_neg]
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · simp only [one_mul, hcneg]
    · rcases (abs_eq hr.le).mp hdabs with hdpos | hdneg
      · simp only [one_mul, hdpos]
      · exact False.elim (hneq (hcneg.trans hdneg.symm))



theorem exists_neck_minimizer_graph_crossing (W : EpsilonNeck g)
    (hε : W.epsilon ≤ 1 / 1000) {U : Set M} (hWU : W.carrier ⊆ U)
    {γ : ℝ → M} {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcenter : γ t = W.center)
    (haout : γ a ∉ W.carrier) (hbout : γ b ∉ W.carrier)
    {f : UnitTwoSphere → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hfb : ∀ p, |f p| < 7 * W.epsilon⁻¹ / 8) :
    ∃ v ∈ Ioo a b,
      γ v ∈ range (fun p : UnitTwoSphere => W.coordinate_map (p, f p)) := by
  obtain ⟨c, hc, d, hd, hcdW, σ, hσ, hcaxis, hdaxis⟩ :=
    exists_neck_minimizer_opposite_levels W hε hWU hat htb hγ hγU hmin
      hcenter haout hbout
  have hApos : 0 < W.epsilon⁻¹ := inv_pos.mpr W.epsilon_pos
  have hbuffer : 7 * W.epsilon⁻¹ / 8 < W.epsilon⁻¹ := by linarith only [hApos]
  have hdom (p : UnitTwoSphere) : f p ∈ Ioo (-W.epsilon⁻¹) W.epsilon⁻¹ :=
    abs_lt.mp ((hfb p).trans hbuffer)
  have hfbσ (p : UnitTwoSphere) : |σ * f p| < 7 * W.epsilon⁻¹ / 8 := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using hfb p
    · simpa only [neg_one_mul, abs_neg] using hfb p
  have hleft : σ * neckGraphHeight W f (γ c) < 0 := by
    change σ * ((W.coordinate_inverse (γ c)).2 - f (W.coordinate_inverse (γ c)).1) < 0
    rw [mul_sub, hcaxis]
    have h := (abs_lt.mp (hfbσ (W.coordinate_inverse (γ c)).1)).1
    linarith only [h, hApos]
  have hright : 0 < σ * neckGraphHeight W f (γ d) := by
    change 0 < σ * ((W.coordinate_inverse (γ d)).2 - f (W.coordinate_inverse (γ d)).1)
    rw [mul_sub, hdaxis]
    have h := (abs_lt.mp (hfbσ (W.coordinate_inverse (γ d)).1)).2
    linarith only [h, hApos]
  obtain ⟨v, hv, hgraph⟩ := exists_neck_graph_crossing W hf hdom
    (hc.2.trans hd.1).le
    (hγ.continuousOn.mono (Icc_subset_Icc hc.1.le hd.2.le)) hcdW hσ hleft hright
  exact ⟨v, ⟨hc.1.trans hv.1, hv.2.trans hd.2⟩, hgraph⟩

end PoincareConjecture.M28
