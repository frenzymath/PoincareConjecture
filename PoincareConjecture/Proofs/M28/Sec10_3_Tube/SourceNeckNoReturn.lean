import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckRegion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckShortening
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckExcursionSubarcs











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28



theorem intrinsic_minimizer_return_stays_in_middle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {U : Set M} (hNU : N.central_sphere ⊆ U)
    {γ : ℝ → M} {a b s t : ℝ}
    (has : a ≤ s) (htb : t ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hs : γ s ∈ N.central_sphere) (ht : γ t ∈ N.central_sphere) :
    MapsTo γ (Icc s t) (N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2)) := by
  intro v hv
  by_contra hmiddle
  obtain ⟨w, hsw, hwv, hsubarc, hheight⟩ :=
    N.exists_first_half_neck_subarc hv.1
      (hγ.continuousOn.mono (Icc_subset_Icc has (hv.2.trans htb))) hs hmiddle
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hsave⟩ :=
    exists_neck_excursion_replacement N hepsilon hNU has le_rfl hsw.le
      (hwv.trans hv.2) htb hγ hγU hs ht hsubarc hheight.ge
  have hminσ : g.pathELength γ a b ≤ g.pathELength σ 0 1 := by
    rw [hmin]
    simpa only [hσ0, hσ1] using
      intrinsicEDist_le_pathELength g zero_le_one hσ hσU
  have hcancel : ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8) ≤ 0 := by
    apply (ENNReal.add_le_add_iff_left hfinite).mp
    simpa only [add_zero] using
      (add_le_add hminσ (le_refl
        (ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 8)))).trans hsave
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (neck_shortening_saving_pos N))) hcancel




theorem exists_source_neck_no_return_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N ∈ S.cover.necks, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          S.path s ∈ N.central_sphere → S.path t ∈ N.central_sphere →
          MapsTo S.path (Icc s t)
            (N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2)) := by
  obtain ⟨epsilonR, hRpos, hRsmall, hregion⟩ := exists_source_neck_region_accuracy.{u}
  let epsilon₀ := min epsilonR neckShorteningEpsilon
  refine ⟨epsilon₀, lt_min hRpos neckShorteningEpsilon_pos,
    (min_le_left _ _).trans hRsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall N hN s hs t ht hsN htN
  have hNU : N.carrier ⊆ S.source_region.carrier := by
    intro x hx
    exact (hregion E S hQ (hsmall.trans (min_le_left _ _))).2.1 ⟨N, hN, hx⟩
  have heps : N.epsilon ≤ neckShorteningEpsilon := by
    rw [S.cover.neck_epsilon N hN, S.cover_epsilon]
    exact hsmall.trans (min_le_right _ _)
  exact intrinsic_minimizer_return_stays_in_middle N heps
    (N.central_sphere_subset.trans hNU) hs.1 ht.2 S.path_smooth
    S.source_region.path_mem S.source_region.finite_length S.source_region.minimizing hsN htN

end PoincareConjecture.M28
