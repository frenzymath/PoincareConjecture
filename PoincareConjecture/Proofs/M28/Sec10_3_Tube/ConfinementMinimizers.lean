import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckEndpointShortening
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizer










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]




theorem exists_confined_sequence_and_minimizer_of_endpoint_crossings
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    {p q : M} (N : Bool → EpsilonNeck g)
    (hsmall : ∀ i, (N i).epsilon ≤ neckShorteningEpsilon)
    (hsphere : ∀ i, (N i).central_sphere ⊆ (U : Set M))
    (hcross : ∀ γ : ℝ → M, γ 0 = p → γ 1 = q →
      ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) →
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
        ∃ (i : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
          γ c ∈ (N i).central_sphere ∧ γ d ∈ (N i).central_sphere ∧
          γ t ∉ (N i).region (-((N i).epsilon⁻¹ / 2)) ((N i).epsilon⁻¹ / 2))
    {η : ℝ → M} {L : ℝ} (hη0 : η 0 = p) (hη1 : η 1 = q)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc (0 : ℝ) 1))
    (hηU : MapsTo η (Icc (0 : ℝ) 1) (U : Set M))
    (hηL : g.pathELength η 0 1 < ENNReal.ofReal L) :
    ∃ paths : ℕ → ℝ → M,
      (∀ k, paths k 0 = p ∧ paths k 1 = q ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (paths k) (Icc (0 : ℝ) 1) ∧
        MapsTo (paths k) (Icc (0 : ℝ) 1) K ∧
        g.pathELength (paths k) 0 1 < ENNReal.ofReal L) ∧
      Tendsto (fun k => g.pathELength (paths k) 0 1) atTop
        (𝓝 (intrinsicEDist g (U : Set M) p q)) ∧
      ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
        MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) ∧
        g.pathELength γ 0 1 = intrinsicEDist g (U : Set M) p q ∧
        g.pathELength γ 0 1 ≠ ⊤ ∧ g.pathELength γ 0 1 < ENNReal.ofReal L := by
  let d := intrinsicEDist g (U : Set M) p q
  let saving (i : Bool) := (N i).scale * (N i).epsilon⁻¹ / 8
  let delta := min (saving false) (saving true)
  have hsaving (i : Bool) : 0 < saving i :=
    div_pos (mul_pos (N i).scale_pos (inv_pos.mpr (N i).epsilon_pos)) (by norm_num)
  have hdelta : 0 < delta := lt_min (hsaving false) (hsaving true)
  have hdelta_le (i : Bool) : delta ≤ saving i := by
    cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hdL : d < ENNReal.ofReal L := by
    simpa only [hη0, hη1] using
      (intrinsicEDist_le_pathELength g zero_le_one hη hηU).trans_lt hηL
  have hdfinite : d ≠ ⊤ := ne_top_of_lt (hdL.trans_le le_top)
  have hnear : d < ENNReal.ofReal (d.toReal + delta) := by
    apply (ENNReal.toReal_lt_toReal hdfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith only [hdelta]
  let ceiling := min L (d.toReal + delta)
  have hceiling : d < ENNReal.ofReal ceiling := by
    change d < ENNReal.ofReal (min L (d.toReal + delta))
    rw [ENNReal.ofReal_min]
    exact lt_min hdL hnear
  obtain ⟨α, hα0, hα1, hα, hαU, hαL⟩ := exists_intrinsic_competitor g hceiling
  obtain ⟨paths, hpaths, htendsto⟩ :=
    exists_intrinsic_minimizing_sequence_of_path g zero_le_one hα hαU hαL
  rw [hα0, hα1] at htendsto
  have hpaths' (k : ℕ) : paths k 0 = p ∧ paths k 1 = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (paths k) (Icc (0 : ℝ) 1) ∧
      MapsTo (paths k) (Icc (0 : ℝ) 1) K ∧
      g.pathELength (paths k) 0 1 < ENNReal.ofReal L := by
    obtain ⟨h0, h1, hsmooth, hU, hlength⟩ := hpaths k
    have hp : paths k 0 = p := h0.trans hα0
    have hq : paths k 1 = q := h1.trans hα1
    refine ⟨hp, hq, hsmooth, ?_,
      hlength.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
    intro t ht
    by_contra hnot
    obtain ⟨i, c, e, hc, hct, hte, he, hcsphere, hesphere, hexit⟩ :=
      hcross (paths k) hp hq hsmooth.continuousOn hU t ht hnot
    obtain ⟨σ, hσ0, hσ1, hσ, hσU, hshort⟩ :=
      exists_endpoint_neck_shortening (N i) (hsmall i) (hsphere i)
        hc hct hte he hsmooth hU hcsphere hesphere hexit
    have hdσ : d ≤ g.pathELength σ 0 1 := by
      simpa only [hσ0, hσ1, hp, hq] using
        intrinsicEDist_le_pathELength g zero_le_one hσ hσU
    have hsave : d + ENNReal.ofReal delta ≤ g.pathELength (paths k) 0 1 :=
      (add_le_add hdσ (ENNReal.ofReal_le_ofReal (hdelta_le i))).trans hshort
    have hbound : g.pathELength (paths k) 0 1 < d + ENNReal.ofReal delta := by
      have hh := hlength.trans_le (ENNReal.ofReal_le_ofReal
        (show ceiling ≤ d.toReal + delta from min_le_right _ _))
      simpa only [ENNReal.ofReal_add ENNReal.toReal_nonneg hdelta.le,
        ENNReal.ofReal_toReal hdfinite] using hh
    exact (not_lt_of_ge hsave) hbound
  obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγlength, hγfinite⟩ :=
    exists_intrinsic_minimizer_of_compact_sequence g U hK hKU
      (fun k => (hpaths' k).2.2.1) (fun k => (hpaths' k).1)
      (fun k => (hpaths' k).2.1) (fun k => (hpaths' k).2.2.2.1)
      (fun k => (hpaths' k).2.2.2.2) htendsto
  exact ⟨paths, hpaths', htendsto, γ, hγ0, hγ1, hγ, hγU, hγlength, hγfinite,
    hγlength ▸ hdL⟩

end PoincareConjecture.M28
