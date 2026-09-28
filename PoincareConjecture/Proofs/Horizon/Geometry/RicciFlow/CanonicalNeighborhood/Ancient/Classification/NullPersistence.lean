import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.CompactProduct
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {C : Type*} [TopologicalSpace C] [CompactSpace C] [Nonempty C]

theorem not_strictlyPositiveSectionalCurvature_of_compact_prod_real
    (e : (C × ℝ) ≃ₜ M) (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) :
    ¬ D.StrictlyPositiveSectionalCurvature := by
  let : Nonempty M := ⟨e (Classical.choice inferInstance, 0)⟩
  let : NoncompactSpace M := e.isClosedEmbedding.noncompactSpace
  intro hpos
  obtain ⟨P⟩ := g.exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    D hcomplete hpos
  exact Poincare.Topology.not_nonempty_homeomorph_compact_prod_real_euclidean_three
    ⟨e.trans P.euclidean.symm.toHomeomorph⟩

theorem exists_null_plane_of_compact_prod_real
    (e : (C × ℝ) ≃ₜ M) (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) :
    ∃ (x : M) (v w : TangentSpace (𝓡 3) x),
      g.inner x v v = 1 ∧ g.inner x w w = 1 ∧ g.inner x v w = 0 ∧
        D.curvatureTensor x v w v w = 0 := by
  have hpos := g.not_strictlyPositiveSectionalCurvature_of_compact_prod_real
    e D hcomplete
  dsimp only [LeviCivitaData.StrictlyPositiveSectionalCurvature] at hpos
  push Not at hpos
  obtain ⟨x, v, w, hv, hw, hvw, hnonpos⟩ := hpos
  refine ⟨x, v, w, hv, hw, hvw, le_antisymm ?_ (hsec x v w)⟩
  simpa only [LeviCivitaData.sectionalCurvature, hv, hw, hvw, one_mul,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using hnonpos

theorem exists_null_plane_of_compact_prod_real_local_isometry
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (e : (C × ℝ) ≃ₜ M) (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (h : RiemannianMetric 3 N)
    (D' : LeviCivitaData h) {p : M → N} (hp : ContMDiff (𝓡 3) (𝓡 3) ∞ p)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (p x) (mfderiv (𝓡 3) (𝓡 3) p x v)
        (mfderiv (𝓡 3) (𝓡 3) p x w))
    (hsec : D'.NonnegativeSectionalCurvature) :
    ∃ (x : N) (v w : TangentSpace (𝓡 3) x),
      h.inner x v v = 1 ∧ h.inner x w w = 1 ∧ h.inner x v w = 0 ∧
        D'.curvatureTensor x v w v w = 0 := by
  have hcurv := fun (x : M) (u v w z : TangentSpace (𝓡 3) x) =>
    D.curvatureTensor_eq_of_local_isometry D' isOpen_univ hp.contMDiffOn
      (fun y _ => hinner y) (mem_univ x) u v w z
  have hsec' : D.NonnegativeSectionalCurvature := by
    intro x v w
    rw [hcurv x v w v w]
    exact hsec (p x) _ _
  obtain ⟨x, v, w, hv, hw, hvw, hzero⟩ :=
    g.exists_null_plane_of_compact_prod_real e D hcomplete hsec'
  refine ⟨p x, mfderiv (𝓡 3) (𝓡 3) p x v, mfderiv (𝓡 3) (𝓡 3) p x w,
    ?_, ?_, ?_, ?_⟩
  · exact (hinner x v v).symm.trans hv
  · exact (hinner x w w).symm.trans hw
  · exact (hinner x v w).symm.trans hvw
  · exact (hcurv x v w v w).symm.trans hzero

end PoincareConjecture.RiemannianMetric
