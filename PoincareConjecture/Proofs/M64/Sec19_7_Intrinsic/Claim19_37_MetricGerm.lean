import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_ExtensionBalls













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture



theorem m64Intrinsic_model_chart_coefficients
    (G : RiemannianMetric 2 AnnulusCoordinates) (p : AnnulusCoordinates) :
    G.pullbackCoefficients (extChartAt (𝓡 2) p).symm = G.euclideanCoefficients := by
  ext x v w
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe]
  change G.inner x (mfderiv (𝓡 2) (𝓡 2) id x v) (mfderiv (𝓡 2) (𝓡 2) id x w) =
    G.inner x v w
  rw [mfderiv_id]
  rfl




theorem m64Intrinsic_geodesic_of_metric_germ
    (G H : RiemannianMetric 2 AnnulusCoordinates)
    {q : ℝ → AnnulusCoordinates} {S : Set ℝ}
    (hgeo : G.IsGeodesicOn q S)
    (hmetric : ∀ t ∈ S, G.euclideanCoefficients =ᶠ[𝓝 (q t)] H.euclideanCoefficients) :
    H.IsGeodesicOn q S := by
  intro t ht
  obtain ⟨p, Q, W, hlocal⟩ := hgeo t ht
  have hQt : Q t = q t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using hlocal.self_of_nhds.1.symm
  have hQcont : ContinuousAt Q t := hlocal.self_of_nhds.2.2.1.continuousAt
  have hm : G.euclideanCoefficients =ᶠ[𝓝 (Q t)] H.euclideanCoefficients := by
    rw [hQt]
    exact hmetric t ht
  have hnear : ∀ᶠ r in 𝓝 t,
      G.euclideanCoefficients =ᶠ[𝓝 (Q r)] H.euclideanCoefficients :=
    hQcont.tendsto.eventually hm.eventually_nhds
  refine ⟨p, Q, W, ?_⟩
  filter_upwards [hlocal, hnear] with r hr hmr
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_⟩
  have hGamma : coordinateChristoffel G.euclideanCoefficients (Q r) (W r) (W r) =
      coordinateChristoffel H.euclideanCoefficients (Q r) (W r) (W r) := by
    simp only [coordinateChristoffel, hmr.self_of_nhds, hmr.fderiv_eq]
  simpa only [m64Intrinsic_model_chart_coefficients, hGamma] using hr.2.2.2



theorem m64Intrinsic_isOpen_metric_agreement
    (G H : RiemannianMetric 2 AnnulusCoordinates) :
    IsOpen {p | G.euclideanCoefficients =ᶠ[𝓝 p] H.euclideanCoefficients} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  exact hp.eventually_nhds



theorem m64Intrinsic_exists_metric_agreement_tube
    (N : IntrinsicAnnulus) (G : RiemannianMetric 2 AnnulusCoordinates)
    (hG : ∀ p ∈ standardAnnulusDomain,
      G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients)
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : Continuous u) {a b : ℝ}
    {J : Set ℝ} (hJ : IsOpen J) (hJsub : Icc (0 : ℝ) b ⊆ J)
    (himage : ∀ t ∈ Icc (0 : ℝ) b, u (a, t) ∈ standardAnnulusDomain) :
    ∃ S I : Set ℝ, IsOpen S ∧ IsOpen I ∧ a ∈ S ∧ Icc (0 : ℝ) b ⊆ I ∧
      I ⊆ J ∧ ∀ s ∈ S, ∀ t ∈ I,
        G.euclideanCoefficients =ᶠ[𝓝 (u (s, t))] N.metric.euclideanCoefficients := by
  let Omega := {z : ℝ × ℝ |
    G.euclideanCoefficients =ᶠ[𝓝 (u z)] N.metric.euclideanCoefficients} ∩ (univ ×ˢ J)
  have hOmega : IsOpen Omega :=
    ((m64Intrinsic_isOpen_metric_agreement G N.metric).preimage hu).inter
      (isOpen_univ.prod hJ)
  have hsub : ({a} : Set ℝ) ×ˢ Icc (0 : ℝ) b ⊆ Omega := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hsa : s = a := mem_singleton_iff.mp hs
    subst s
    exact ⟨hG _ (himage t ht), mem_univ a, hJsub ht⟩
  obtain ⟨S, I, hS, hI, haS, hIcc, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hOmega hsub
  have ha : a ∈ S := haS (mem_singleton a)
  exact ⟨S, I, hS, hI, ha, hIcc,
    fun t ht => (hprod (show (a, t) ∈ S ×ˢ I from ⟨ha, ht⟩)).2.2,
    fun s hs t ht => (hprod (show (s, t) ∈ S ×ˢ I from ⟨hs, ht⟩)).1⟩

end PoincareConjecture
