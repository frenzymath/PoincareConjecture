import PoincareConjecture.Proofs.M11.OrdinaryIdentification
import PoincareConjecture.Proofs.M11.BoxCylinder





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M] [Nonempty M]

theorem ordinaryProduct_timeVector_box (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (b : M) (q : (smoothInterval I).Point × spatialChartDomain (n := n) b) :
    mfderiv (spacetimeModel n) (spacetimeModel n) (ordinaryProductIdentification g I hg)
        (q.1, spatialChartInverse b q.2) ((smoothInterval I).positiveTangent q.1, 0) =
      (adaptedSpacetime (ordinaryAtlas g I hg)).timeVector
        (ordinaryProductIdentification g I hg (q.1, spatialChartInverse b q.2)) := by
  let D := ordinaryProductIdentification g I hg
  let j : (smoothInterval I).Point × spatialChartDomain (n := n) b →
      (smoothInterval I).Point × M := Prod.map id (spatialChartInverse b)
  have hj : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ j :=
    contMDiff_fst.prodMk ((spatialChartInverse_smooth b).comp contMDiff_snd)
  have hd : mfderiv (spacetimeModel n) (spacetimeModel n) j q
      ((smoothInterval I).positiveTangent q.1, 0) =
      ((smoothInterval I).positiveTangent q.1, 0) := by
    rw [mfderiv_prodMap mdifferentiableAt_id
      ((spatialChartInverse_smooth b q.2).mdifferentiableAt (by simp)), mfderiv_id]
    apply Prod.ext
    · rfl
    · change mfderiv (𝓡 n) (𝓡 n) (spatialChartInverse b) q.2 0 = 0
      exact map_zero _
  have h := mfderiv_comp_apply q ((D.contMDiff (j q)).mdifferentiableAt (by simp))
    ((hj q).mdifferentiableAt (by simp)) ((smoothInterval I).positiveTangent q.1, 0)
  rw [hd] at h
  exact h.symm.trans (adaptedTimeVector_box (ordinaryAtlas g I hg) b q).symm

theorem ordinaryProduct_timeVector (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (p : (smoothInterval I).Point × M) :
    mfderiv (spacetimeModel n) (spacetimeModel n) (ordinaryProductIdentification g I hg) p
        ((smoothInterval I).positiveTangent p.1, 0) =
      (adaptedSpacetime (ordinaryAtlas g I hg)).timeVector
        (ordinaryProductIdentification g I hg p) := by
  let x : spatialChartDomain (n := n) p.2 :=
    ⟨chartAt (EuclideanSpace ℝ (Fin n)) p.2 p.2, mem_chart_target _ p.2⟩
  have hx : spatialChartInverse p.2 x = p.2 :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p.2).left_inv (mem_chart_source _ p.2)
  have h := ordinaryProduct_timeVector_box g I hg p.2 (p.1, x)
  rw [hx] at h
  exact h

noncomputable def ordinaryProductCylinder (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    CompatibleSpacetimeCylinder (adaptedSpacetime (ordinaryAtlas g I hg))
      (smoothInterval I) M where
  interval_subset := Subset.rfl
  toSpacetime := ordinaryProductIdentification g I hg
  embedding := (ordinaryProductIdentification g I hg).toHomeomorph.isEmbedding
  time_eq := fun _ ↦ rfl
  worldline_smooth := fun x ↦ (ordinaryProductIdentification g I hg).contMDiff.comp
    (contMDiff_id.prodMk contMDiff_const)
  worldline_derivative := by
    intro t x
    have h := mfderiv_comp_apply t
      (((ordinaryProductIdentification g I hg).contMDiff (t, x)).mdifferentiableAt (by simp))
      ((contMDiff_id.prodMk contMDiff_const : ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞
        (fun s : (smoothInterval I).Point ↦ (s, x))) t |>.mdifferentiableAt (by simp))
      ((smoothInterval I).positiveTangent t)
    simp only [id_eq] at h
    rw [mfderiv_prod_left] at h
    exact h.trans (ordinaryProduct_timeVector g I hg (t, x))
  smooth := (ordinaryProductIdentification g I hg).contMDiff
  differential_injective := fun p ↦
    ((ordinaryProductIdentification g I hg).mfderivToContinuousLinearEquiv (by simp) p).injective

end PoincareConjecture.Proofs.M11
