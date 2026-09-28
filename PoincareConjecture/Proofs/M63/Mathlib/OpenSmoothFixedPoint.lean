import PoincareConjecture.Proofs.M03.Existence.QuasilinearDeTurckNative

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

theorem exists_contDiffOn_fixedPoint_of_open_domain
    {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (R : P × X → X) {O : Set (P × X)} (hO : IsOpen O)
    {p : P} {x : X} (hp : (p, x) ∈ O) (hR : ContDiffOn ℝ ∞ R O)
    (hfix : R (p, x) = x)
    (hsmall : ‖(fderiv ℝ R (p, x)).comp (ContinuousLinearMap.inr ℝ P X)‖ < 1) :
    ∃ (U : Set P) (V : Set (P × X)) (u : P → X),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ (p, x) ∈ V ∧ u p = x ∧
      ContDiffOn ℝ ∞ u U ∧
      (∀ q ∈ U, (q, u q) ∈ O ∧ R (q, u q) = u q) ∧
      ∀ z ∈ V, R z = z.2 ↔ u z.1 = z.2 := by
  obtain ⟨u, hup, hu, hueq, hunique⟩ :=
    PoincareConjecture.QuasilinearDeTurckNative.exists_contDiffAt_fixedPoint R
      (k := 1) (by norm_num) ((hR.contDiffAt (hO.mem_nhds hp)).of_le (by simp))
      hfix hsmall
  have hD : ContinuousAt (fun z : P × X =>
      ‖(fderiv ℝ R z).comp (ContinuousLinearMap.inr ℝ P X)‖) (p, x) :=
    (((hR.continuousOn_fderiv_of_isOpen hO (by simp)).continuousAt
      (hO.mem_nhds hp)).clm_comp continuousAt_const).norm
  have hgraph : Tendsto (fun q : P => (q, u q)) (𝓝 p) (𝓝 (p, x)) := by
    simpa only [hup, id_eq] using (continuousAt_id.prodMk hu.continuousAt).tendsto
  have hnear : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 1 u q ∧ (q, u q) ∈ O ∧
      ‖(fderiv ℝ R (q, u q)).comp (ContinuousLinearMap.inr ℝ P X)‖ < 1 ∧
      R (q, u q) = u q := by
    filter_upwards [hu.eventually (by simp), hgraph.eventually (hO.mem_nhds hp),
      hgraph.eventually (hD.eventually (isOpen_Iio.mem_nhds hsmall)), hueq]
      with q hq hqO hqsmall hqfix
    exact ⟨hq, hqO, hqsmall, hqfix⟩
  obtain ⟨U, hUS, hU, hpU⟩ := mem_nhds_iff.mp hnear
  obtain ⟨V, hVS, hV, hpV⟩ := mem_nhds_iff.mp hunique
  refine ⟨U, V, u, hU, hpU, hV, hpV, hup, ?_, ?_, fun z hz => hVS hz⟩
  · apply hU.contDiffOn_iff.mpr
    intro q hq
    obtain ⟨v, _hvq, hv, _hveq, hvunique⟩ :=
      PoincareConjecture.QuasilinearDeTurckNative.exists_contDiffAt_fixedPoint R
        (k := ∞) (by simp) (hR.contDiffAt (hO.mem_nhds (hUS hq).2.1))
        (hUS hq).2.2.2 (hUS hq).2.2.1
    apply hv.congr_of_eventuallyEq
    have hgraphq : ContinuousAt (fun z : P => (z, u z)) q :=
      continuousAt_id.prodMk (hUS hq).1.continuousAt
    filter_upwards [hU.mem_nhds hq, hgraphq.eventually hvunique] with z hz hzu
    exact (hzu.mp (hUS hz).2.2.2).symm
  · intro q hq
    exact ⟨(hUS hq).2.1, (hUS hq).2.2.2⟩
