import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Nonterminal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.OneDimensional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

open Poincare.VolumeComparison

theorem radialDensity_cross_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    {p : M} {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t | t • v ∈ Metric.ball 0 R} ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (t • v))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ ∧
        g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {t s : ℝ} (ht : t ∈ Ioo 0 R) (hs : s ∈ Ioo 0 R) (hts : t ≤ s) :
    let S := localMinimizingSet (fun v => g.edist p (e v)) R
    let T := terminalRadialPoints S R
    let F := fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)) *
      (S \ T).indicator (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x))
        (r • (θ : EuclideanSpace ℝ (Fin n)))
    F s * ENNReal.ofReal (modelS κ t ^ (n - 1)) ≤
      F t * ENNReal.ofReal (modelS κ s ^ (n - 1)) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  by_cases hn1 : n = 1
  · subst n
    simpa only [Nat.sub_self, pow_zero, ENNReal.ofReal_one, one_mul, mul_one] using
      (polarDensity_antitone_one g p he
        (fun v hv t ht => ((hgeo v hv).2 t ht).1)
        (fun v hv t ht => ((hgeo v hv).2 t ht).2) θ) ht hs hts
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : 0 < m := by omega
  dsimp only
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  change (ENNReal.ofReal (s ^ m) * (S \ T).indicator _ (s • (θ : EuclideanSpace ℝ (Fin (m + 1))))) * _ ≤
    (ENNReal.ofReal (t ^ m) * (S \ T).indicator _ (t • (θ : EuclideanSpace ℝ (Fin (m + 1))))) * _
  by_cases hsS : s • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T
  · have hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S := by
      intro v hv a ha0 ha1
      exact radial_minimizing_star g he hv
        (fun u hu => ((hgeo v hv.1).2 u hu).1)
        (fun u hu => ((hgeo v hv.1).2 u hu).2) a ha0 ha1
    have htS : t • (θ : EuclideanSpace ℝ (Fin (m + 1))) ∈ S \ T := by
      have h := smul_mem_sdiff_terminalRadialPoints hstar hsS
        (div_pos ht.1 hs.1) ((div_le_one hs.1).mpr hts)
      simpa only [smul_smul, div_mul_cancel₀ _ hs.1.ne'] using h
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    have hreal := g.polarDensity_cross_le_on_nonterminal D hm hR hκ hL he he0 hed
      (fun v hv => (hgeo v hv).1)
      (fun v hv t ht => ((hgeo v hv).2 t ht).1)
      (fun v hv t ht => ((hgeo v hv).2 t ht).2)
      (by simpa only [Nat.cast_succ, add_sub_cancel_right, neg_mul] using hRic)
      θ hθ ht hs hts hsS
    simpa only [Nat.succ_sub_one, indicator_of_mem hsS, indicator_of_mem htS,
      ENNReal.ofReal_mul' (pow_nonneg (modelS_pos hκ ht.1).le m),
      ENNReal.ofReal_mul' (pow_nonneg (modelS_pos hκ hs.1).le m),
      ENNReal.ofReal_mul (pow_nonneg hs.1.le m),
      ENNReal.ofReal_mul (pow_nonneg ht.1.le m)] using ENNReal.ofReal_le_ofReal hreal
  · simp only [indicator_of_notMem hsS, mul_zero, zero_mul, zero_le]

theorem antitoneOn_radialDensity_div_modelS
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    {p : M} {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ)
    {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)}
    {e : EuclideanSpace ℝ (Fin n) → M}
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R)) (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t | t • v ∈ Metric.ball 0 R} ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (t • v))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ ∧
        g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    AntitoneOn (fun t : ℝ =>
      (t ^ (n - 1) *
        (localMinimizingSet (fun v => g.edist p (e v)) R \
          terminalRadialPoints (localMinimizingSet (fun v => g.edist p (e v)) R) R).indicator
          (g.pullbackVolumeDensity e) (t • (θ : EuclideanSpace ℝ (Fin n)))) /
        modelS κ t ^ (n - 1)) (Ioo 0 R) := by
  classical
  let S := localMinimizingSet (fun v => g.edist p (e v)) R
  let T := terminalRadialPoints S R
  let ρ := (S \ T).indicator (g.pullbackVolumeDensity e)
  have hρ (v) : 0 ≤ ρ v := by
    by_cases hv : v ∈ S \ T
    · simpa only [ρ, indicator_of_mem hv] using
        (show 0 ≤ g.pullbackVolumeDensity e v from Real.sqrt_nonneg _)
    · simp only [ρ, indicator_of_notMem hv, le_refl]
  have hof (v) : ENNReal.ofReal (ρ v) =
      (S \ T).indicator (fun x => ENNReal.ofReal (g.pullbackVolumeDensity e x)) v := by
    by_cases hv : v ∈ S \ T <;> simp [ρ, hv]
  intro t ht s hs hts
  apply (div_le_div_iff₀ (pow_pos (modelS_pos hκ hs.1) _)
    (pow_pos (modelS_pos hκ ht.1) _)).mpr
  change (s ^ (n - 1) * ρ (s • (θ : EuclideanSpace ℝ (Fin n)))) *
      modelS κ t ^ (n - 1) ≤
    (t ^ (n - 1) * ρ (t • (θ : EuclideanSpace ℝ (Fin n)))) * modelS κ s ^ (n - 1)
  have hc := g.radialDensity_cross_le D hn hR hκ hL he he0 hed hgeo hRic θ ht hs hts
  change (ENNReal.ofReal (s ^ (n - 1)) * _ ) * _ ≤
    (ENNReal.ofReal (t ^ (n - 1)) * _ ) * _ at hc
  have htρ : 0 ≤ t ^ (n - 1) * ρ (t • (θ : EuclideanSpace ℝ (Fin n))) :=
    mul_nonneg (pow_nonneg ht.1.le _) (hρ _)
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg htρ (pow_nonneg (modelS_nonneg hκ hs.1.le) _))).mp
  simpa only [ENNReal.ofReal_mul' (pow_nonneg (modelS_nonneg hκ ht.1.le) (n - 1)),
    ENNReal.ofReal_mul' (pow_nonneg (modelS_nonneg hκ hs.1.le) (n - 1)),
    ENNReal.ofReal_mul (pow_nonneg ht.1.le (n - 1)),
    ENNReal.ofReal_mul (pow_nonneg hs.1.le (n - 1)), hof] using hc

end PoincareConjecture.RiemannianMetric
