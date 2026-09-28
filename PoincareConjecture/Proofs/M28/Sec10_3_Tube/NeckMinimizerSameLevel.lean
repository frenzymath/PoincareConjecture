import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckMinimizerTraversal

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem exists_two_contained_collar_levels_same_level (W : EpsilonNeck g)
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

theorem exists_neck_minimizer_same_level (W : EpsilonNeck g)
    (hε : W.epsilon ≤ (1 / 1000 : ℝ)) {U : Set M} (hWU : W.carrier ⊆ U)
    {γ : ℝ → M} {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcenter : γ t = W.center)
    (haout : γ a ∉ W.carrier) (hbout : γ b ∉ W.carrier)
    {x : M} (hx : x ∈ W.carrier) :
    ∃ c ∈ Ioo a t, ∃ d ∈ Ioo t b, ∃ v ∈ Icc c d,
      MapsTo γ (Icc c d) W.carrier ∧
      MapsTo γ (Icc (min v t) (max v t)) W.carrier ∧
      (W.coordinate_inverse (γ v)).2 = (W.coordinate_inverse x).2 ∧
      intrinsicEDist g W.carrier x (γ v) ≤
        ENNReal.ofReal
          (W.scale * Real.sqrt (1 + W.epsilon) * Real.sqrt 2 *
            (Real.pi + 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A : ℝ := W.epsilon⁻¹
  have hApos : 0 < A := by
    dsimp [A]
    exact inv_pos.mpr W.epsilon_pos
  have hA : (1000 : ℝ) ≤ A := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    dsimp [A] at h ⊢
    rw [mul_inv_cancel₀ W.epsilon_pos.ne'] at h
    linarith only [h]
  have hxheight : |(W.coordinate_inverse x).2| < A := by
    dsimp [A]
    exact abs_lt.mpr (W.coordinate_inverse_mem x hx).2
  have hhalf : A / 2 < A := by linarith only [hApos]
  have hmax : max (A / 2) |(W.coordinate_inverse x).2| < A :=
    max_lt hhalf hxheight
  obtain ⟨r, hrlo, hrhi⟩ := exists_between hmax
  have hrpos : 0 < r := by
    exact (lt_of_lt_of_le (by positivity : 0 < A / 2) (le_max_left _ _)).trans hrlo
  obtain ⟨c, hc, d, hd, hcdW, hcabs, hdabs⟩ :=
    exists_two_contained_collar_levels_same_level W hrpos (by simpa [A] using hrhi)
      hat htb hγ.continuousOn hcenter haout hbout
  have hfinite : g.pathELength γ a b ≠ ⊤ := by
    rw [pathELength_eq_integral_fixed_segment_speed g hγ le_rfl
      (hat.trans htb).le le_rfl]
    exact ENNReal.ofReal_ne_top
  have hcd : c < d := hc.2.trans hd.1
  have hminimum := pathELength_eq_intrinsicEDist_subsegment g hc.1.le hcd.le hd.2.le
    hγ hγU hfinite hmin
  have hneq : (W.coordinate_inverse (γ c)).2 ≠
      (W.coordinate_inverse (γ d)).2 := by
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
    have hshort : intrinsicEDist g U (γ c) (γ d) ≤
        ENNReal.ofReal (20 * W.scale) :=
      hupper.trans (ENNReal.ofReal_le_ofReal hscaled)
    have htzero : (W.coordinate_inverse (γ t)).2 = 0 := by
      rw [hcenter]
      exact (W.mem_central_sphere_iff_of_mem_carrier
        (W.central_sphere_subset W.center_on_central_sphere)).mp
        W.center_on_central_sphere
    have hcost := path_axial_displacement_le W hc.2.le
      (hγ.mono (Icc_subset_Icc hc.1.le htb.le))
      (fun s hs => hcdW ⟨hs.1, hs.2.trans hd.1.le⟩)
    rw [htzero, zero_sub, abs_neg, hcabs] at hcost
    have hlong : ENNReal.ofReal ((W.scale / 2) * r) ≤
        g.pathELength γ c d :=
      hcost.trans (Manifold.pathELength_mono le_rfl hd.1.le)
    rw [hminimum] at hlong
    have hrhalf : A / 2 < r := (le_max_left _ _).trans_lt hrlo
    have hgap : 20 * W.scale < (W.scale / 2) * r := by
      have hbase : (20 : ℝ) < (1 / 2 : ℝ) * r := by
        nlinarith only [hA, hrhalf]
      have hs := mul_lt_mul_of_pos_left hbase W.scale_pos
      nlinarith only [hs]
    have hpositive : 0 < (W.scale / 2) * r :=
      mul_pos (div_pos W.scale_pos (by norm_num)) hrpos
    exact (not_lt_of_ge (hlong.trans hshort))
      ((ENNReal.ofReal_lt_ofReal_iff hpositive).mpr hgap)
  have hheight : ContinuousOn
      (fun s : ℝ => (W.coordinate_inverse (γ s)).2) (Icc c d) :=
    (continuous_snd.comp_continuousOn W.coordinate_inverse_smooth.continuousOn).comp
      (hγ.continuousOn.mono (Icc_subset_Icc hc.1.le hd.2.le)) hcdW
  have hxr : |(W.coordinate_inverse x).2| < r :=
    (le_max_right (A / 2) |(W.coordinate_inverse x).2|).trans_lt hrlo
  rcases (abs_eq hrpos.le).mp hcabs with hcpos | hcneg
  · rcases (abs_eq hrpos.le).mp hdabs with hdpos | hdneg
    · exact False.elim (hneq (hcpos.trans hdpos.symm))
    · have htarget : (W.coordinate_inverse x).2 ∈ Icc
          ((W.coordinate_inverse (γ d)).2)
          ((W.coordinate_inverse (γ c)).2) := by
        rw [hdneg, hcpos]
        exact ⟨(abs_lt.mp hxr).1.le, (abs_lt.mp hxr).2.le⟩
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc' hcd.le hheight htarget
      have hvW : γ v ∈ W.carrier := hcdW hv
      have hdist := W.intrinsicEDist_le_axial_add hx hvW
      have hveq' : (W.coordinate_inverse (γ v)).2 =
          (W.coordinate_inverse x).2 := hveq
      have hzero : (W.coordinate_inverse (γ v)).2 -
          (W.coordinate_inverse x).2 = 0 := by rw [hveq']; ring
      rw [hzero, abs_zero, zero_add] at hdist
      have hsub' : Icc (min v t) (max v t) ⊆ Icc c d := by
        intro z hz
        exact ⟨(le_min hv.1 hc.2.le).trans hz.1,
          hz.2.trans (max_le hv.2 hd.1.le)⟩
      refine ⟨c, hc, d, hd, v, hv, hcdW,
        (fun z hz => hcdW (hsub' hz)), hveq, ?_⟩
      convert hdist using 1
      all_goals ring_nf
  · rcases (abs_eq hrpos.le).mp hdabs with hdpos | hdneg
    · have htarget : (W.coordinate_inverse x).2 ∈ Icc
          ((W.coordinate_inverse (γ c)).2)
          ((W.coordinate_inverse (γ d)).2) := by
        rw [hcneg, hdpos]
        exact ⟨(abs_lt.mp hxr).1.le, (abs_lt.mp hxr).2.le⟩
      obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc hcd.le hheight htarget
      have hvW : γ v ∈ W.carrier := hcdW hv
      have hdist := W.intrinsicEDist_le_axial_add hx hvW
      have hveq' : (W.coordinate_inverse (γ v)).2 =
          (W.coordinate_inverse x).2 := hveq
      have hzero : (W.coordinate_inverse (γ v)).2 -
          (W.coordinate_inverse x).2 = 0 := by rw [hveq']; ring
      rw [hzero, abs_zero, zero_add] at hdist
      have hsub' : Icc (min v t) (max v t) ⊆ Icc c d := by
        intro z hz
        exact ⟨(le_min hv.1 hc.2.le).trans hz.1,
          hz.2.trans (max_le hv.2 hd.1.le)⟩
      refine ⟨c, hc, d, hd, v, hv, hcdW,
        (fun z hz => hcdW (hsub' hz)), hveq, ?_⟩
      convert hdist using 1
      all_goals ring_nf
    · exact False.elim (hneq (hcneg.trans hdneg.symm))

end PoincareConjecture.M28
