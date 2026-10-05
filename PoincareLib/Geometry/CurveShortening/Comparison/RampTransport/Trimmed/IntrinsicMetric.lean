import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.Immersion.Metric
import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Trimmed.PolarDescent
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Closed.StripDifferential

/-! Genuine intrinsic metrics on the trimmed actual annulus.
Source: MT Lemma 19.31, pp. 464-466; trimmed-intrinsic-transport derivation,
Section 8. All strip immersion and metric-extension data are constructed. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareMT

open M64Uniformization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

/-- The actual periodic closed-C1 immersed minimum has, after every
positive trim, a genuine frozen IntrinsicAnnulus realization. The
pullback metric agrees on neighborhoods, and both boundary maps remain
literal slices of the original annulus. Source: MT Lemma 19.31,
pp. 464-466; transport derivation, Section 8. -/
theorem m64Annulus_exists_trimmed_intrinsic_metric (A : M64Annulus g c0 c1)
    (hAc : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p))
    {eps : ℝ} (hpos : 0 < eps) (hsmall : eps < 1 / 2) :
    ∃ (N : IntrinsicAnnulus) (F : LoopPlane → M),
      (∀ z : ℝ × ℝ, 0 < z.1 →
        F (scalarCoverMap z) = A.map (m64TrimmedCoverCoordinate eps z)) ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ F (m64TrimmedAnnulusNeighborhood eps) ∧
      (∀ p ∈ m64TrimmedAnnulusNeighborhood eps,
        Function.Injective (mfderiv (𝓡 2) (𝓡 n) F p)) ∧
      (∀ p ∈ standardAnnulusDomain, ∀ᶠ q in 𝓝 p, ∀ u v,
        N.metric.inner q u v = g.inner (F q) (mfderiv (𝓡 2) (𝓡 n) F q u)
          (mfderiv (𝓡 2) (𝓡 n) F q v)) ∧
      (∀ theta : ℝ, F (intrinsicAnnulusBoundary 1 theta) = A.map (annulusPoint theta eps)) ∧
      ∀ theta : ℝ, F (intrinsicAnnulusBoundary 2 theta) =
        A.map (annulusPoint theta (1 - eps)) := by
  have hstrip : ∀ p ∈ m64AnnulusOpenStrip,
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) A.map p) := by
    intro p hp
    have hsub : m64AnnulusOpenStrip ⊆ {q : LoopPlane | q 1 ∈ Icc (0 : ℝ) 1} :=
      fun _ hq => ⟨hq.1.le, hq.2.le⟩
    have h := M64.annulus_strip_within_injective A hAc hinj p (hsub hp)
    rw [mfderivWithin_of_mem_nhds
      (mem_of_superset (isOpen_m64AnnulusOpenStrip.mem_nhds hp) hsub)] at h
    exact h
  obtain ⟨F, hdesc, hU, hSU, hF, hFi, hlo, hhi⟩ :=
    m64_exists_trimmed_polar_descent A.periodic hAi hstrip hpos hsmall
  have hS : IsClosed standardAnnulusDomain :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  obtain ⟨h, D, hmetric⟩ := m64_exists_induced_metric_near g hS hU hSU hF hFi
  exact ⟨⟨h, D⟩, F, hdesc, hF, hFi, hmetric, hlo, hhi⟩

end PoincareMT
