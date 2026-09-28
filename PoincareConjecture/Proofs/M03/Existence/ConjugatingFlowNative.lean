import PoincareConjecture.Proofs.M03.Existence.MetricPerturbationNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckGaugeSign
import PoincareConjecture.Proofs.M03.Existence.FamilyEquation
import PoincareConjecture.Proofs.M03.Existence.PullbackMetricDerivativeNative












set_option autoImplicit false

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)





theorem hasDerivWithinAt_pullbackMetric_of_jointFDeriv_eq
    (g : ℝ → RiemannianMetric n M)
    (Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hsmooth : ∀ s : ℝ,
      ContMDiff (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun y : M => Bundle.TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) y
          (pinner (g s) (Φ s) y)))
    {J : Set ℝ} {t : ℝ} {x : M}
    {u v : TangentSpace (𝓡 n) x}
    {L : (ℝ × ℝ) →L[ℝ] ℝ} {d : ℝ}
    (hF : HasFDerivWithinAt
      (fun q : ℝ × ℝ =>
        (g q.1).inner (Φ q.2 x)
          (mfderiv (𝓡 n) (𝓡 n) (Φ q.2) x u)
          (mfderiv (𝓡 n) (𝓡 n) (Φ q.2) x v))
      L (J ×ˢ J) (t, t))
    (hvalue : L (1, 1) = d) :
    HasDerivWithinAt
      (fun s : ℝ =>
        (pullbackMetric (g s) (Φ s) (hsmooth s)).inner x u v)
      d J t := by
  have hdiag := hasDerivWithinAt_pullbackMetric_of_jointFDeriv
    (g := g) (Φ := Φ) (hsmooth := hsmooth) hF
  exact hdiag.congr_deriv hvalue

theorem hasDerivWithinAt_pullbackMetric_add_gauge_zero
    (g : ℝ → RiemannianMetric n M)
    (Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hsmooth : ∀ s : ℝ,
      ContMDiff (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun y : M => Bundle.TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) y
          (pinner (g s) (Φ s) y)))
    {J : Set ℝ} {t : ℝ} {x : M}
    {u v : TangentSpace (𝓡 n) x}
    {L : (ℝ × ℝ) →L[ℝ] ℝ} {q : ℝ → ℝ}
    (hF : HasFDerivWithinAt
      (fun r : ℝ × ℝ =>
        (g r.1).inner (Φ r.2 x)
          (mfderiv (𝓡 n) (𝓡 n) (Φ r.2) x u)
          (mfderiv (𝓡 n) (𝓡 n) (Φ r.2) x v))
      L (J ×ˢ J) (t, t))
    (hGauge : HasDerivWithinAt q (-L (1, 1)) J t) :
    HasDerivWithinAt
      (fun s : ℝ =>
        (pullbackMetric (g s) (Φ s) (hsmooth s)).inner x u v + q s)
      0 J t := by
  have hpull := hasDerivWithinAt_pullbackMetric_of_jointFDeriv
    (g := g) (Φ := Φ) hsmooth hF
  exact (hpull.add hGauge).congr_deriv (by ring)

theorem exists_metricFamily_of_intervalIntegral_source
    (g₀ : RiemannianMetric n M) {T : ℝ} (hT : 0 < T)
    (P : SmallMetricPath g₀ (Set.Ico (0 : ℝ) T))
    (h : ℝ → ∀ x : M, TangentSpace (𝓡 n) x →
      TangentSpace (𝓡 n) x → ℝ)
    (hcont : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      ContinuousOn (fun s ↦ h s x u v) (Set.Ico (0 : ℝ) T))
    (hint : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (x : M)
      (u v : TangentSpace (𝓡 n) x),
      (P.metric t).inner x u v = g₀.inner x u v +
        ∫ s in (0 : ℝ)..t, h s x u v)
    (D : ∀ t : ℝ, LeviCivitaData (P.metric t))
    (hEq : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (x : M)
      (u v : TangentSpace (𝓡 n) x),
      h t x u v = -2 * (D t).ricci x u v) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g₀ ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D' : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D'.ricci x u v) (Set.Ico 0 T) t := by
  refine ⟨T, hT, P.metric, P.metric_initial, P.metric_isSmoothFamilyOn, ?_⟩
  intro t ht D' x u v
  have hd := PoincareConjecture.DeTurckNative.hasDerivWithinAt_metric_of_intervalIntegral_Ico
    (g₀ := g₀) (g := P.metric) (h := h) (T := T) hcont hint ht x u v
  rw [hEq t ht x u v] at hd
  exact ricciEquation_connectionIndependent t ht (D t) D' hd

end PoincareConjecture

end
