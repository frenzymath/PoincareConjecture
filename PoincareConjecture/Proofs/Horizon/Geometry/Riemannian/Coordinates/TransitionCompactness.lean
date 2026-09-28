import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

private theorem norm_bound_of_uniform_convergence_on_compact
    {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    {K : Set X} (hK : IsCompact K) {f : ℕ → X → Y} {f₀ : X → Y}
    (hf : ∀ k, ContinuousOn (f k) K) (hf₀ : ContinuousOn f₀ K)
    (hlim : TendstoUniformlyOn f f₀ atTop K) :
    ∃ C : ℝ, ∀ k x, x ∈ K → ‖f k x‖ ≤ C := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf₀
  have htail : ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x‖ ≤ B + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim 1 zero_lt_one] with k hk x hx
    have he : ‖f k x‖ ≤ ‖f k x - f₀ x‖ + ‖f₀ x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f k x - f₀ x) (f₀ x)
    have hd : dist (f k x) (f₀ x) < 1 := by simpa only [dist_comm] using hk x hx
    have hd' : ‖f k x - f₀ x‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hd
    linarith [hB x hx]
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  choose b hb using fun k => hK.exists_bound_of_continuousOn (hf k)
  let C := ∑ k ∈ Finset.range N, max (b k) 0
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => le_max_right (b k) 0
  refine ⟨max (B + 1) 0 + C, ?_⟩
  intro k x hx
  by_cases hk : N ≤ k
  · exact (hN k hk x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right hC))
  · have hbC : max (b k) 0 ≤ C :=
      Finset.single_le_sum (fun j _ => le_max_right (b j) 0)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hk))
    exact (hb k x hx).trans ((le_max_left _ _).trans
      (hbC.trans (le_add_of_nonneg_left (le_max_right _ _))))

private theorem eventually_lower_bound_of_positive_limit
    {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    {Bseq : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {B : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < B x v v)
    (hlim : TendstoUniformlyOn Bseq B atTop K) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v,
      a * ‖v‖ ^ 2 ≤ Bseq k x v v := by
  let : NormedAddCommGroup
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hB hpos
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (a / 2) (by positivity)]
    with k hk x hx v
  have hd : ‖Bseq k x - B x‖ ≤ a / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le
  have herr : |Bseq k x v v - B x v v| ≤ a / 2 * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖Bseq k x - B x‖ * ‖v‖ * ‖v‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using (Bseq k x - B x).le_opNorm₂ v v
      _ ≤ a / 2 * ‖v‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hd (mul_nonneg (norm_nonneg v) (norm_nonneg v))
  have hh := (abs_le.mp herr).1
  linarith [hlower x hx v]



theorem locallyEventuallyBoundedDerivatives_of_metric_convergence
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hV : IsOpen V)
    {Aseq Bseq : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {A B : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAseq : LocallyEventuallyContDiff U Aseq)
    (hBseq : LocallyEventuallyContDiff V Bseq)
    (hf : LocallyEventuallyContDiff U f)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B V)
    (hAsymm : ∀ k x, x ∈ U → ∀ u v, Aseq k x u v = Aseq k x v u)
    (hBsymm : ∀ k x, x ∈ V → ∀ u v, Bseq k x u v = Bseq k x v u)
    (hApos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < A x v v)
    (hBpos : ∀ x ∈ V, ∀ v, v ≠ 0 → 0 < B x v v)
    (hAlim : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Aseq k)) (iteratedFDeriv ℝ m A) atTop K)
    (hBlim : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Bseq k)) (iteratedFDeriv ℝ m B) atTop K)
    (htarget : ∀ K, IsCompact K → K ⊆ U → ∃ L,
      IsCompact L ∧ L ⊆ V ∧ ∀ᶠ k in atTop, MapsTo (f k) K L)
    (hmetric : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ u v,
        Bseq k (f k x) (fderiv ℝ (f k) x u) (fderiv ℝ (f k) x v) = Aseq k x u v) :
    LocallyEventuallyBoundedDerivatives U f := by
  have hAconv := locallyUniformly_of_tendsto_zeroJet hU (hAlim 0)
  have hBconv := locallyUniformly_of_tendsto_zeroJet hV (hBlim 0)
  have hbound : LocallyEventuallyBoundedDerivatives U f := by
    intro K hK hKU m
    obtain ⟨W, hW, hKW, hWU, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨L, hL, hLV, hmap⟩ := htarget (closure W) hWcompact hWU
    obtain ⟨Z, hZ, hLZ, hZV, hZcompact⟩ :=
      exists_open_between_and_isCompact_closure hL hV hLV
    obtain ⟨a, ha, hAlow⟩ := eventually_lower_bound_of_positive_limit hWcompact
      (hA.continuousOn.mono hWU) (fun x hx => hApos x (hWU hx))
      ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hWcompact).mp
        (hAconv.mono hWU))
    obtain ⟨b, hb, hBlow⟩ := eventually_lower_bound_of_positive_limit hZcompact
      (hB.continuousOn.mono hZV) (fun x hx => hBpos x (hZV hx))
      ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hZcompact).mp
        (hBconv.mono hZV))
    have hevent := (hAseq (closure W) hWcompact hWU).and
      ((hBseq (closure Z) hZcompact hZV).and
        ((hf (closure W) hWcompact hWU).and
          (hAlow.and (hBlow.and (hmap.and (hmetric (closure W) hWcompact hWU))))))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    have hN' (k : ℕ) := hN (k + N) (Nat.le_add_left N k)
    have hWA (k : ℕ) : ContDiffOn ℝ ∞ (Aseq (k + N)) W := by
      obtain ⟨O, _, hWO, hs⟩ := (hN' k).1
      exact hs.mono (subset_closure.trans hWO)
    have hZB (k : ℕ) : ContDiffOn ℝ ∞ (Bseq (k + N)) Z := by
      obtain ⟨O, _, hZO, hs⟩ := (hN' k).2.1
      exact hs.mono (subset_closure.trans hZO)
    have hWf (k : ℕ) : ContDiffOn ℝ ∞ (f (k + N)) W := by
      obtain ⟨O, _, hWO, hs⟩ := (hN' k).2.2.1
      exact hs.mono (subset_closure.trans hWO)
    have hjet : ∀ q, ∃ C,
        (∀ k x, x ∈ W → ‖iteratedFDeriv ℝ q (Aseq (k + N)) x‖ ≤ C) ∧
        (∀ k x, x ∈ Z → ‖iteratedFDeriv ℝ q (Bseq (k + N)) x‖ ≤ C) := by
      intro q
      have hAc (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ q (Aseq (k + N))) (closure W) := by
        obtain ⟨O, hO, hWO, hs⟩ := (hN' k).1
        intro x hx
        exact ((hs x (hWO hx)).contDiffAt (hO.mem_nhds (hWO hx))).continuousAt_iteratedFDeriv
          (by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top)) |>.continuousWithinAt
      have hBc (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ q (Bseq (k + N))) (closure Z) := by
        obtain ⟨O, hO, hZO, hs⟩ := (hN' k).2.1
        intro x hx
        exact ((hs x (hZO hx)).contDiffAt (hO.mem_nhds (hZO hx))).continuousAt_iteratedFDeriv
          (by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top)) |>.continuousWithinAt
      have hAc₀ : ContinuousOn (iteratedFDeriv ℝ q A) (closure W) := by
        intro x hx
        exact ((hA x (hWU hx)).contDiffAt (hU.mem_nhds (hWU hx))).continuousAt_iteratedFDeriv
          (by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top)) |>.continuousWithinAt
      have hBc₀ : ContinuousOn (iteratedFDeriv ℝ q B) (closure Z) := by
        intro x hx
        exact ((hB x (hZV hx)).contDiffAt (hV.mem_nhds (hZV hx))).continuousAt_iteratedFDeriv
          (by exact_mod_cast (show (q : ℕ∞) ≤ ⊤ from le_top)) |>.continuousWithinAt
      obtain ⟨C, hC⟩ := norm_bound_of_uniform_convergence_on_compact hWcompact hAc hAc₀
        (fun E hE => (tendsto_add_atTop_nat N).eventually (hAlim q _ hWcompact hWU E hE))
      obtain ⟨D, hD⟩ := norm_bound_of_uniform_convergence_on_compact hZcompact hBc hBc₀
        (fun E hE => (tendsto_add_atTop_nat N).eventually (hBlim q _ hZcompact hZV E hE))
      exact ⟨max C D, fun k x hx => (hC k x (subset_closure hx)).trans (le_max_left _ _),
        fun k x hx => (hD k x (subset_closure hx)).trans (le_max_right _ _)⟩
    obtain ⟨C, hC⟩ := uniform_derivative_bounds_of_local_isometries hW hZ
      (hZcompact.isBounded.subset subset_closure) hWA hZB hWf
      (fun k x hx => hAsymm (k + N) x (hWU (subset_closure hx)))
      (fun k x hx => hBsymm (k + N) x (hZV (subset_closure hx)))
      (lt_min ha hb)
      (fun k x hx v => (mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg ‖v‖)).trans
        ((hN' k).2.2.2.1 x (subset_closure hx) v))
      (fun k x hx v => (mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg ‖v‖)).trans
        ((hN' k).2.2.2.2.1 x (subset_closure hx) v))
      hjet (fun k x hx => hLZ ((hN' k).2.2.2.2.2.1 (subset_closure hx)))
      (fun k x hx => (hN' k).2.2.2.2.2.2 x (subset_closure hx)) m
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop N] with k hk x hx
    simpa only [Nat.sub_add_cancel hk] using hC (k - N) x (hKW hx)
  exact hbound





theorem exists_smooth_isometry_limit_of_metric_convergence
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hV : IsOpen V)
    {Aseq Bseq : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {A B : EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAseq : LocallyEventuallyContDiff U Aseq)
    (hBseq : LocallyEventuallyContDiff V Bseq)
    (hf : LocallyEventuallyContDiff U f)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B V)
    (hAsymm : ∀ k x, x ∈ U → ∀ u v, Aseq k x u v = Aseq k x v u)
    (hBsymm : ∀ k x, x ∈ V → ∀ u v, Bseq k x u v = Bseq k x v u)
    (hApos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < A x v v)
    (hBpos : ∀ x ∈ V, ∀ v, v ≠ 0 → 0 < B x v v)
    (hAlim : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Aseq k)) (iteratedFDeriv ℝ m A) atTop K)
    (hBlim : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Bseq k)) (iteratedFDeriv ℝ m B) atTop K)
    (htarget : ∀ K, IsCompact K → K ⊆ U → ∃ L,
      IsCompact L ∧ L ⊆ V ∧ ∀ᶠ k in atTop, MapsTo (f k) K L)
    (hmetric : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ u v,
        Bseq k (f k x) (fderiv ℝ (f k) x u) (fderiv ℝ (f k) x v) = Aseq k x u v) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        ContDiffOn ℝ ∞ f₀ U ∧ MapsTo f₀ U V ∧
        (∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f (σ k))) (iteratedFDeriv ℝ m f₀) atTop K) ∧
        ∀ x ∈ U, ∀ u v,
          B (f₀ x) (fderiv ℝ f₀ x u) (fderiv ℝ f₀ x v) = A x u v := by
  have hbound := locallyEventuallyBoundedDerivatives_of_metric_convergence
    hU hV hAseq hBseq hf hA hB hAsymm hBsymm hApos hBpos hAlim hBlim htarget hmetric
  obtain ⟨σ, hσ, f₀, hf₀, hlim⟩ :=
    exists_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
      hU f hf hbound
  have hflim := locallyUniformly_of_tendsto_zeroJet hU (hlim 0)
  have hfV : MapsTo f₀ U V := by
    intro x hx
    obtain ⟨L, hL, hLV, hmap⟩ := htarget {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    apply hLV
    exact hL.isClosed.mem_of_tendsto (hflim.tendsto_at hx)
      ((hσ.tendsto_atTop.eventually hmap).mono fun k hk => hk (mem_singleton x))
  refine ⟨σ, hσ, f₀, hf₀, hfV, hlim, ?_⟩
  apply pullback_eq_of_tendsto_jets hU hV
    (Aseq := fun k => Aseq (σ k)) (Bseq := fun k => Bseq (σ k))
    (fun m K hK hKU E hE => hσ.tendsto_atTop.eventually (hAlim m K hK hKU E hE))
    (fun m K hK hKV E hE => hσ.tendsto_atTop.eventually (hBlim m K hK hKV E hE))
    hlim hB.continuousOn hfV
  intro x hx
  exact (hσ.tendsto_atTop.eventually
    (hmetric {x} isCompact_singleton (singleton_subset_iff.mpr hx))).mono
    (fun k hk => hk x (mem_singleton x))



theorem exists_common_smooth_isometry_limit_of_metric_convergence
    {d : ℕ} {U V : ℕ → Set (EuclideanSpace ℝ (Fin d))}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    {Aseq Bseq : ℕ → ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {A B : ℕ → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {f : ℕ → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hAseq : ∀ i, LocallyEventuallyContDiff (U i) (Aseq i))
    (hBseq : ∀ i, LocallyEventuallyContDiff (V i) (Bseq i))
    (hf : ∀ i, LocallyEventuallyContDiff (U i) (f i))
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (U i))
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) (V i))
    (hAsymm : ∀ i k x, x ∈ U i → ∀ u v, Aseq i k x u v = Aseq i k x v u)
    (hBsymm : ∀ i k x, x ∈ V i → ∀ u v, Bseq i k x u v = Bseq i k x v u)
    (hApos : ∀ i x, x ∈ U i → ∀ v, v ≠ 0 → 0 < A i x v v)
    (hBpos : ∀ i x, x ∈ V i → ∀ v, v ≠ 0 → 0 < B i x v v)
    (hAlim : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Aseq i k)) (iteratedFDeriv ℝ m (A i)) atTop K)
    (hBlim : ∀ i m K, IsCompact K → K ⊆ V i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (Bseq i k)) (iteratedFDeriv ℝ m (B i)) atTop K)
    (htarget : ∀ i K, IsCompact K → K ⊆ U i → ∃ L,
      IsCompact L ∧ L ⊆ V i ∧ ∀ᶠ k in atTop, MapsTo (f i k) K L)
    (hmetric : ∀ i K, IsCompact K → K ⊆ U i → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ u v,
        Bseq i k (f i k x) (fderiv ℝ (f i k) x u) (fderiv ℝ (f i k) x v) =
          Aseq i k x u v) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f₀ : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ i, ContDiffOn ℝ ∞ (f₀ i) (U i)) ∧
        (∀ i, MapsTo (f₀ i) (U i) (V i)) ∧
        (∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f i (σ k))) (iteratedFDeriv ℝ m (f₀ i)) atTop K) ∧
        ∀ i x, x ∈ U i → ∀ u v,
          B i (f₀ i x) (fderiv ℝ (f₀ i) x u) (fderiv ℝ (f₀ i) x v) = A i x u v := by
  have hbound (i : ℕ) := locallyEventuallyBoundedDerivatives_of_metric_convergence
    (hU i) (hV i) (hAseq i) (hBseq i) (hf i) (hA i) (hB i)
    (hAsymm i) (hBsymm i) (hApos i) (hBpos i) (hAlim i) (hBlim i) (htarget i) (hmetric i)
  obtain ⟨σ, hσ, f₀, hf₀, hlim⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
      hU f hf hbound
  have hfV (i : ℕ) : MapsTo (f₀ i) (U i) (V i) := by
    intro x hx
    obtain ⟨L, hL, hLV, hmap⟩ := htarget i {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    apply hLV
    exact hL.isClosed.mem_of_tendsto
      ((locallyUniformly_of_tendsto_zeroJet (hU i) (hlim i 0)).tendsto_at hx)
      ((hσ.tendsto_atTop.eventually hmap).mono fun k hk => hk (mem_singleton x))
  refine ⟨σ, hσ, f₀, hf₀, hfV, hlim, ?_⟩
  intro i
  apply pullback_eq_of_tendsto_jets (hU i) (hV i)
    (Aseq := fun k => Aseq i (σ k)) (Bseq := fun k => Bseq i (σ k))
    (fun m K hK hKU E hE => hσ.tendsto_atTop.eventually (hAlim i m K hK hKU E hE))
    (fun m K hK hKV E hE => hσ.tendsto_atTop.eventually (hBlim i m K hK hKV E hE))
    (hlim i) (hB i).continuousOn (hfV i)
  intro x hx
  exact (hσ.tendsto_atTop.eventually
    (hmetric i {x} isCompact_singleton (singleton_subset_iff.mpr hx))).mono
    (fun k hk => hk x (mem_singleton x))

end PoincareConjecture.CoordinateTransition
