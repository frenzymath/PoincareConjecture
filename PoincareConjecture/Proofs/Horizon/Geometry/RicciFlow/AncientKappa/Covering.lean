import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Covering.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [T3Space N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

theorem AncientKappaNoncollapsed.of_covering
    {F : RicciFlow n M (Iic 0)} {G : RicciFlow n N (Iic 0)} {p : M → N}
    (hp : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p) (hc : IsCoveringMap p)
    (hinner : ∀ t ≤ 0, ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      (F.metric t).inner x v w = (G.metric t).inner (p x)
        (mfderiv (𝓡 n) (𝓡 n) p x v) (mfderiv (𝓡 n) (𝓡 n) p x w))
    {κ : ℝ} (hnc : AncientKappaNoncollapsed G κ) :
    AncientKappaNoncollapsed F κ := by
  intro r₀ hr₀ t ht x r hr hrr₀ hbound
  have hball := (F.metric t).image_ball_of_covering (G.metric t) hp hc (hinner t ht) x r
  have hbase : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ y ∈ (G.metric t).ball (p x) r,
      |(G.connection s).curvatureTensorNorm y| ≤ r⁻¹ ^ 2 := by
    intro s hs y hy
    obtain ⟨z, hz, rfl⟩ := hball.symm ▸ hy
    rw [← (F.connection s).curvatureTensorNorm_eq_of_local_isometry
      (G.connection s) isOpen_univ hp.contMDiff.contMDiffOn
      (fun q _ => hinner s (hs.2.trans ht) q) (mem_univ z)]
    exact hbound s hs z hz
  have hvol := calibratedMetricVolume_image_le_of_metric_pullback
    (F.metric t) (G.metric t) hp.contMDiff (hinner t ht) ((F.metric t).ball x r)
  rw [hball] at hvol
  exact (hnc r₀ hr₀ t ht (p x) r hr hrr₀ hbase).trans hvol

theorem AncientKappaSolution.exists_lift_of_covering
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [ConnectedSpace M] [ConnectedSpace N]
    (K : AncientKappaSolution n N) (p : M → N)
    (hp : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ p) (hc : IsCoveringMap p)
    (hsurj : Function.Surjective p) :
    ∃ L : AncientKappaSolution n M, L.kappa = K.kappa ∧
      ∀ t : ℝ, ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
        (L.flow.metric t).inner x v w = (K.flow.metric t).inner (p x)
          (mfderiv (𝓡 n) (𝓡 n) p x v) (mfderiv (𝓡 n) (𝓡 n) p x w) := by
  let F := K.flow.pullbackWithConnection p hp (fun t =>
    ((K.flow.metric t).pullbackOfLocalDiffeomorph p hp).leviCivitaData)
  have hnorm (t : ℝ) (x : M) :
      (F.connection t).curvatureTensorNorm x = (K.flow.connection t).curvatureTensorNorm (p x) :=
    (F.connection t).curvatureTensorNorm_eq_of_local_isometry (K.flow.connection t)
      isOpen_univ hp.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)
  let L : AncientKappaSolution n M :=
    { flow := F
      kappa := K.kappa
      kappa_pos := K.kappa_pos
      complete := fun t ht =>
        (K.flow.metric t).metricComplete_pullbackOfLocalDiffeomorph p hp hc (K.complete t ht)
      nonnegative_curvature_operator := fun t ht x =>
        ((F.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
          (K.flow.connection t) isOpen_univ hp.contMDiff.contMDiffOn
          (fun _ _ _ _ => rfl) (mem_univ x)).mpr (K.nonnegative_curvature_operator t ht (p x))
      bounded_curvature := by
        intro t ht
        obtain ⟨B, hB, hbound⟩ := K.bounded_curvature t ht
        exact ⟨B, hB, fun x => by rw [hnorm]; exact hbound (p x)⟩
      nonflat := by
        intro t ht
        obtain ⟨x, hx⟩ := K.nonflat t ht
        obtain ⟨y, rfl⟩ := hsurj x
        exact ⟨y, by rw [hnorm]; exact hx⟩
      noncollapsed := K.noncollapsed.of_covering hp hc (fun _ _ _ _ _ => rfl) }
  exact ⟨L, rfl, fun _ _ _ _ => rfl⟩

end PoincareConjecture
