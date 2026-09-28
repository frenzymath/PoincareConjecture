import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative
import PoincareConjecture.Proofs.M03.Existence.EuclideanGraphRellichNative

set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.EuclideanGraphRellichNative

open EuclideanTranslationNative DeTurckDomainRegularityNative

theorem weakPair_mem_closure_derivativeGraphSet {n : ℕ}
    (u : ScalarL2 n) (d : Fin n → ScalarL2 n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (huK : ∀ᵐ y ∂volume, y ∉ K → u y = 0)
    (hweak : ∀ i (test : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)),
      ⟪d i, test.toLp 2 volume⟫_ℝ =
        -(∫ y, u y * fderiv ℝ test y (EuclideanSpace.single i 1)))
    {r : ℝ} (hr : 0 < r) :
    (u, d) ∈ closure (derivativeGraphSet (cthickening r K)) := by
  obtain ⟨S, hsupport, hvalue, hderiv⟩ :=
    exists_schwartz_approximation_of_weak_derivatives u d hK huK hweak hr
  let graph (j : ℕ) : GraphAmbient n :=
    ((S j).toLp 2 volume, fun i =>
      (∂_{EuclideanSpace.single i (1 : ℝ)} (S j)).toLp 2 volume)
  have hmem (j : ℕ) : graph j ∈ derivativeGraphSet (cthickening r K) := by
    refine ⟨S j, (S j).smooth 1, (S j).memLp 2 volume,
      fun i => (∂_{EuclideanSpace.single i (1 : ℝ)} (S j)).memLp 2 volume,
      ?_, rfl, fun _ => rfl⟩
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx ((hsupport j).2 h))
  have hlim : Tendsto graph atTop (𝓝 (u, d)) :=
    hvalue.prodMk_nhds (tendsto_pi_nhds.mpr hderiv)
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

theorem totallyBounded_of_supported_weakDerivatives {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {S : Set (ScalarL2 n)} {R D : ℝ} (hD : 0 ≤ D)
    (hvalue : ∀ u ∈ S, ‖u‖ ≤ R)
    (hweak : ∀ u ∈ S, ∃ d : Fin n → ScalarL2 n,
      (∀ i, ‖d i‖ ≤ D) ∧ (∀ᵐ y ∂volume, y ∉ K → u y = 0) ∧
      ∀ i (test : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)),
        ⟪d i, test.toLp 2 volume⟫_ℝ =
          -(∫ y, u y * fderiv ℝ test y (EuclideanSpace.single i 1))) :
    TotallyBounded S := by
  apply (totallyBounded_completedGraph_value (hK.cthickening (r := 1))
    (R := max R D) (le_max_of_le_right hD)).subset
  intro u hu
  obtain ⟨d, hd, hsupport, hpair⟩ := hweak u hu
  refine ⟨(u, d), ⟨weakPair_mem_closure_derivativeGraphSet u d hK hsupport hpair
    (by norm_num : (0 : ℝ) < 1), ?_⟩, rfl⟩
  rw [mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le_max (hvalue u hu) ((pi_norm_le_iff_of_nonneg hD).mpr hd)

end PoincareConjecture.EuclideanGraphRellichNative
