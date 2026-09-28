import PoincareConjecture.Proofs.M03.Existence.MetricFamilyProducerNative
import PoincareConjecture.Proofs.M03.Existence.WithinConjugatingFlowNative








set_option autoImplicit false

open Set Manifold
open scoped ContDiff Bundle

noncomputable section

namespace PoincareConjecture.DeTurckFamilyRecoveryNative

open MetricFamilyProducerNative

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]

def ofDeTurckFamily {g0 : RiemannianMetric n M} {T₀ : ℝ} (hT₀ : 0 < T₀)
    (g : ℝ → RiemannianMetric n M)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Ico 0 T₀))
    (hg0 : g 0 = g0)
    (hpde : ∀ t ∈ Ico 0 T₀, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (deTurckRHS g0 (g t) x u v) (Ico 0 T₀) t) :
    DeTurckConjugatingData g0 := Classical.choice <| by
  obtain ⟨T, hT, hbound, Phi, hPhi0, hPhi, hgen⟩ :=
    WithinConjugatingFlowNative.exists_neg_intrinsicDeTurck_family
      (fun t => connection (g t)) (connection g0) hT₀
      (contMDiffOn_deTurckField g0 hg)
  have hTT₀ : T ≤ T₀ := by linarith
  have hsubset : Ico 0 T ⊆ Ico 0 T₀ :=
    fun _ ht => ⟨ht.1, lt_of_lt_of_le ht.2 hTT₀⟩
  have hgrestrict : RiemannianMetric.IsSmoothFamilyOn g (Ico 0 T) :=
    hg.mono (prod_mono hsubset subset_rfl)
  have hrestrict : ∀ t ∈ Ico 0 T, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (deTurckRHS g0 (g t) x u v) (Ico 0 T) t :=
    fun t ht x u v => (hpde t (hsubset ht) x u v).mono hsubset
  exact ⟨DeTurckConjugatingData.ofFamilies hT g Phi hgrestrict hPhi hg0 hPhi0
    hrestrict hgen⟩

theorem exists_metricFamily {g0 : RiemannianMetric n M} {T₀ : ℝ}
    (hT₀ : 0 < T₀) (g : ℝ → RiemannianMetric n M)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Ico 0 T₀))
    (hg0 : g 0 = g0)
    (hpde : ∀ t ∈ Ico 0 T₀, ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (deTurckRHS g0 (g t) x u v) (Ico 0 T₀) t) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ (D : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s => (g s).inner x u v)
          (-2 * D.ricci x u v) (Ico 0 T) t :=
  IntegralGaugeRecovery.exists_metricFamily
    (ofDeTurckFamily hT₀ g hg hg0 hpde).integralCertificate

end PoincareConjecture.DeTurckFamilyRecoveryNative

end
