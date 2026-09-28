import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff













set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem EpsilonNeck.axial_width_le_pathELength
    (N : EpsilonNeck g) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hcarrier : MapsTo γ (Icc a b) N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
      |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) ≤
      g.pathELength γ a b := by
  let k := N.scale * Real.sqrt (1 - N.epsilon)
  let F : ℝ → ℝ := fun t => k * (N.coordinate_inverse (γ t)).2
  have hk : 0 ≤ k := mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  have hi := (N.coordinate_inverse_smooth.of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).comp hγ hcarrier
  have hheight : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun t => (N.coordinate_inverse (γ t)).2) (Icc a b) :=
    fun t ht => (hi t ht).snd
  have hF : ContDiffOn ℝ 1 F (Icc a b) :=
    contDiffOn_const.mul (contMDiffOn_iff_contDiffOn.mp hheight)
  have hleft : ‖F b - F a‖ₑ = ENNReal.ofReal
      (k * |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) := by
    rw [Real.enorm_eq_ofReal_abs]
    dsimp only [F]
    rw [← mul_sub, abs_mul, abs_of_nonneg hk]
  change ENNReal.ofReal
    (k * |(N.coordinate_inverse (γ b)).2 - (N.coordinate_inverse (γ a)).2|) ≤ _
  rw [← hleft, g.pathELength_eq_lintegral_tangentNorm]
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hF hab).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have houter := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds (hcarrier ht'))).snd.mdifferentiableAt (by simp)
  have hinner := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hd : HasDerivAt (fun s => (N.coordinate_inverse (γ s)).2)
      (mvfderiv (𝓡 3) (fun x => (N.coordinate_inverse x).2) (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)) t := by
    set_option backward.isDefEq.respectTransparency false in
      exact (houter.hasMFDerivAt.comp t hinner.hasMFDerivAt).hasFDerivAt.hasDerivAt
  rw [(hd.const_mul k).deriv, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hk]
  exact ENNReal.ofReal_le_ofReal (N.axial_mvfderiv_bound (hcarrier ht') _)




theorem CapCertificate.end_width_le_pathELength
    (C : CapCertificate g) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hstart : γ a ∈ C.closed_core) (hout : γ b ∉ C.carrier) :
    ENNReal.ofReal (2 * C.epsilon⁻¹ * C.end_neck.scale *
      Real.sqrt (1 - C.epsilon)) ≤ g.pathELength γ a b := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let N := C.end_neck
  let L := C.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hKU : C.closed_core ⊆ C.carrier := by
    rw [C.closed_core_eq_complement_end]
    exact sdiff_subset
  have hKN : Disjoint C.closed_core N.carrier := by
    apply disjoint_left.mpr
    intro x hx hxN
    rw [C.closed_core_eq_complement_end] at hx
    exact hx.2 hxN
  have hslice (t : ℝ) (ht : t ∈ Ioo (-L) L) {x : M}
      (hx : x ∈ N.coordinate_map '' (univ ×ˢ ({t} : Set ℝ))) :
      x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = t := by
    rcases hx with ⟨z, hz, rfl⟩
    have hzt : z.2 = t := mem_singleton_iff.mp hz.2
    have hzN : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hN, hzt]
      exact ht
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hzN⟩, ?_⟩
    rw [N.coordinate_inverse_map z hzN]
    exact hzt
  have hwidth (r : ℝ) (hr : r ∈ Ioo 0 L) :
      ENNReal.ofReal (2 * r * N.scale * Real.sqrt (1 - C.epsilon)) ≤
        g.pathELength γ a b := by
    have hrp : r ∈ Ioo (-L) L := ⟨by linarith [hr.1], hr.2⟩
    have hrm : -r ∈ Ioo (-L) L := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    let Kp := C.carrier \ N.region r L
    let Up := C.closed_core ∪ N.region (-L) r
    let Sp := N.coordinate_map '' (univ ×ˢ ({r} : Set ℝ))
    let Km := C.carrier \ N.region (-r) L
    let Sm := N.coordinate_map '' (univ ×ˢ ({-r} : Set ℝ))
    have htop := C.end_neck_lower_cut_topology hrp
    change Kp ⊆ C.carrier ∧ IsOpen Up ∧ closure Up = Kp ∧ interior Kp = Up ∧
      frontier Up = Sp ∧ frontier Kp = Sp ∧ _ at htop
    obtain ⟨hKpU, hUp, hclUp, hintKp, _, hfrontKp, _⟩ := htop
    have hfrontKm : frontier Km = Sm :=
      (C.end_neck_lower_cut_topology hrm).2.2.2.2.2.1
    have hKpclosed : IsClosed Kp := (C.isCompact_end_neck_lower_cut hrp).isClosed
    have hKmclosed : IsClosed Km := (C.isCompact_end_neck_lower_cut hrm).isClosed
    have hUpKp : Up ⊆ Kp := by
      rw [← hclUp]
      exact subset_closure
    have hstartUp : γ a ∈ Up := Or.inl hstart
    have hstartKm : γ a ∈ Km :=
      ⟨hKU hstart, fun hx => disjoint_left.mp hKN hstart hx.1⟩
    let S := Icc a b ∩ γ ⁻¹' Upᶜ
    have hSclosed : IsClosed S :=
      hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hUp.isClosed_compl
    have hSne : S.Nonempty :=
      ⟨b, ⟨⟨hab, le_rfl⟩, fun hbU => hout (hKpU (hUpKp hbU))⟩⟩
    have hSbdd : BddBelow S := ⟨a, fun _ ht => ht.1.1⟩
    let β := sInf S
    have hβS : β ∈ S := hSclosed.csInf_mem hSne hSbdd
    have haβ : a < β := lt_of_le_of_ne hβS.1.1 (by
      intro heq
      exact hβS.2 (heq ▸ hstartUp))
    have hbefore : MapsTo γ (Ico a β) Up := by
      intro t ht
      by_contra hnot
      have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hβS.1.2⟩, hnot⟩
      exact (not_le_of_gt ht.2) (csInf_le hSbdd htS)
    have hβKp : γ β ∈ Kp := by
      have hpre : IsClosed (Icc a b ∩ γ ⁻¹' Kp) :=
        hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hKpclosed
      have hsub : Ico a β ⊆ Icc a b ∩ γ ⁻¹' Kp :=
        fun t ht => ⟨⟨ht.1, ht.2.le.trans hβS.1.2⟩, hUpKp (hbefore ht)⟩
      have hmem : β ∈ Icc a b ∩ γ ⁻¹' Kp := by
        apply hpre.closure_subset_iff.mpr hsub
        rw [closure_Ico (ne_of_lt haβ)]
        exact ⟨haβ.le, le_rfl⟩
      exact hmem.2
    have hβslice : γ β ∈ Sp := by
      rw [← hfrontKp]
      refine ⟨subset_closure hβKp, ?_⟩
      rw [hintKp]
      exact hβS.2
    have hβcoord := hslice r hrp hβslice
    have hβKm : γ β ∉ Km := by
      intro hx
      apply hx.2
      refine ⟨hβcoord.1, ?_, ?_⟩ <;> rw [hβcoord.2] <;> linarith [hr.1, hr.2]
    let A := Icc a β ∩ γ ⁻¹' Km
    have hγβ : ContinuousOn γ (Icc a β) :=
      hγ.continuousOn.mono (Icc_subset_Icc le_rfl hβS.1.2)
    have hAclosed : IsClosed A :=
      hγβ.preimage_isClosed_of_isClosed isClosed_Icc hKmclosed
    have hAne : A.Nonempty := ⟨a, ⟨⟨le_rfl, haβ.le⟩, hstartKm⟩⟩
    have hAbdd : BddAbove A := ⟨β, fun _ ht => ht.1.2⟩
    let α := sSup A
    have hαA : α ∈ A := hAclosed.csSup_mem hAne hAbdd
    have hαβ : α < β := lt_of_le_of_ne hαA.1.2 (by
      intro heq
      exact hβKm (heq ▸ hαA.2))
    have hafter : MapsTo γ (Ioc α β) Kmᶜ := by
      intro t ht hmem
      have htA : t ∈ A := ⟨⟨hαA.1.1.trans ht.1.le, ht.2⟩, hmem⟩
      exact (not_le_of_gt ht.1) (le_csSup hAbdd htA)
    have hαfront : γ α ∈ frontier Km := by
      refine ⟨subset_closure hαA.2, ?_⟩
      have hpre : IsClosed (Icc a β ∩ γ ⁻¹' (interior Km)ᶜ) :=
        hγβ.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
      have hsub : Ioc α β ⊆ Icc a β ∩ γ ⁻¹' (interior Km)ᶜ := by
        intro t ht
        exact ⟨⟨hαA.1.1.trans ht.1.le, ht.2⟩,
          fun hi => hafter ht (interior_subset hi)⟩
      have hmem : α ∈ Icc a β ∩ γ ⁻¹' (interior Km)ᶜ := by
        apply hpre.closure_subset_iff.mpr hsub
        rw [closure_Ioc (ne_of_lt hαβ)]
        exact ⟨le_rfl, hαβ.le⟩
      exact hmem.2
    have hαcoord := hslice (-r) hrm (hfrontKm ▸ hαfront)
    have hcarrier : MapsTo γ (Icc α β) N.carrier := by
      intro t ht
      by_cases htα : t = α
      · simpa only [htα] using hαcoord.1
      by_cases htβ : t = β
      · simpa only [htβ] using hβcoord.1
      have hαt : α < t := lt_of_le_of_ne ht.1 (Ne.symm htα)
      have htβ' : t < β := lt_of_le_of_ne ht.2 htβ
      have htU := hKpU (hUpKp (hbefore ⟨hαA.1.1.trans ht.1, htβ'⟩))
      by_contra htN
      exact hafter ⟨hαt, ht.2⟩ ⟨htU, fun h => htN h.1⟩
    have hbound := N.axial_width_le_pathELength hαβ.le
      (hγ.mono (Icc_subset_Icc hαA.1.1 hβS.1.2)) hcarrier
    rw [hβcoord.2, hαcoord.2, hN] at hbound
    have heq : N.scale * Real.sqrt (1 - C.epsilon) * |r - -r| =
        2 * r * N.scale * Real.sqrt (1 - C.epsilon) := by
      rw [abs_of_pos (by linarith [hr.1] : 0 < r - -r)]
      ring
    rw [heq] at hbound
    exact hbound.trans (Manifold.pathELength_mono hαA.1.1 hβS.1.2)
  have hclosed : IsClosed {r : ℝ |
      ENNReal.ofReal (2 * r * N.scale * Real.sqrt (1 - C.epsilon)) ≤
        g.pathELength γ a b} :=
    isClosed_le (ENNReal.continuous_ofReal.comp (by fun_prop)) continuous_const
  have hLmem : L ∈ closure (Ioo (0 : ℝ) L) := by
    rw [closure_Ioo (ne_of_lt hL)]
    exact ⟨hL.le, le_rfl⟩
  exact closure_minimal hwidth hclosed hLmem




theorem CapCertificate.exteriorEDepth_add_end_width_le
    (C : CapCertificate g) {D : Set M} {x : M} (hx : x ∈ interior D)
    (hD : closure D ⊆ C.closed_core) :
    (⨅ y ∈ Dᶜ, g.edist x y) +
      ENNReal.ofReal (2 * C.epsilon⁻¹ * C.end_neck.scale *
        Real.sqrt (1 - C.epsilon)) ≤ C.exteriorEDepth x := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hKU : C.closed_core ⊆ C.carrier := by
    rw [C.closed_core_eq_complement_end]
    exact sdiff_subset
  change Metric.infEDist x Dᶜ + ENNReal.ofReal
    (2 * C.epsilon⁻¹ * C.end_neck.scale * Real.sqrt (1 - C.epsilon)) ≤
      Metric.infEDist x C.carrierᶜ
  apply Metric.le_infEDist.mpr
  intro y hy
  by_contra hnot
  have hlt : g.edist x y < Metric.infEDist x Dᶜ + ENNReal.ofReal
      (2 * C.epsilon⁻¹ * C.end_neck.scale * Real.sqrt (1 - C.epsilon)) :=
    lt_of_not_ge hnot
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hstart : γ 0 ∈ interior D := by simpa only [h0] using hx
  have hout : γ 1 ∉ closure D := by
    intro hz
    exact hy (h1 ▸ hKU (hD hz))
  let S := Icc (0 : ℝ) 1 ∩ γ ⁻¹' (interior D)ᶜ
  have hSclosed : IsClosed S :=
    hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
  have hSne : S.Nonempty :=
    ⟨1, ⟨⟨zero_le_one, le_rfl⟩, fun hz => hout (subset_closure (interior_subset hz))⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun _ ht => ht.1.1⟩
  let σ := sInf S
  have hσS : σ ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hσpos : 0 < σ := lt_of_le_of_ne hσS.1.1 (by
    intro heq
    exact hσS.2 (heq ▸ hstart))
  have hbefore : MapsTo γ (Ico 0 σ) (interior D) := by
    intro t ht
    by_contra hnot
    have htS : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hσS.1.2⟩, hnot⟩
    exact (not_le_of_gt ht.2) (csInf_le hSbdd htS)
  have hσclosure : γ σ ∈ closure D := by
    have hpre : IsClosed (Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure D) :=
      hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
    have hsub : Ico 0 σ ⊆ Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure D := by
      intro t ht
      exact ⟨⟨ht.1, ht.2.le.trans hσS.1.2⟩, subset_closure (interior_subset (hbefore ht))⟩
    have hmem : σ ∈ Icc (0 : ℝ) 1 ∩ γ ⁻¹' closure D := by
      apply hpre.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt hσpos)]
      exact ⟨hσpos.le, le_rfl⟩
    exact hmem.2
  have hσcompl : γ σ ∈ closure Dᶜ := by
    rw [closure_compl]
    exact hσS.2
  have hprefix : Metric.infEDist x Dᶜ ≤ g.pathELength γ 0 σ := by
    rw [← Metric.infEDist_closure]
    apply (Metric.infEDist_le_edist_of_mem hσcompl).trans
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl hσS.1.2)) h0 rfl hσpos.le
  have hsuffix := C.end_width_le_pathELength hσS.1.2
    (hγ.mono (Icc_subset_Icc hσpos.le le_rfl)) (hD hσclosure) (fun hz => hy (h1 ▸ hz))
  have hsum := add_le_add hprefix hsuffix
  have hadd : g.pathELength γ 0 σ + g.pathELength γ σ 1 = g.pathELength γ 0 1 :=
    Manifold.pathELength_add hσpos.le hσS.1.2
  rw [hadd] at hsum
  exact (not_le_of_gt hlength) hsum

end PoincareConjecture
