import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimePullback
import PoincareConjecture.Proofs.M62.Sec19_1_LiftedCurve
import PoincareConjecture.Proofs.M62.Sec19_1_Gauss
import PoincareConjecture.Proofs.M62.Sec19_1_Codazzi
import PoincareConjecture.Proofs.M62.Cor0_3_RegularizedGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62.SpacetimeData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem normal_norm {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    (t : OpenTime a b) (x : ℝ) :
    G.metric.inner (G.liftCurve c (x, t)) (m62SpacetimeNormalDerivative G c t x)
      (m62SpacetimeNormalDerivative G c t x) =
      (F.metric t).inner (c x t) (m62SpatialNormalDerivative F c t x)
        (m62SpatialNormalDerivative F c t x) +
        ((F.connection t).ricci (c x t) (spatialUnitTangent F c t x)
          (m62CurvatureVector F c t x)) ^ 2 := by
  let := G.charts.chartedSpace
  let C := G.charts
  let p := c x t
  let q := G.liftCurve c (x, t)
  let D := F.connection t
  let g := F.metric t
  let v := curveSpeed F c t x
  let X := curveVelocity (n := n) (fun y => c y t) x
  let S := spatialUnitTangent F c t x
  let H := m62CurvatureVector F c t x
  let A := m62SpatialDerivative F c t (m62CurvatureVector F c t) x
  let Ahat := v⁻¹ • G.covariantAlong
    (fun y => G.liftCurve c (y, t)) (m62LiftedCurvature G c t) x
  let Shat := m62LiftedUnitTangent G c t x
  have hmem : (x, (t : ℝ)) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    ⟨mem_univ _, t.property⟩
  have hspace : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : ℝ => (y, (t : ℝ))) x :=
    (differentiableAt_id.prodMk (differentiableAt_const (t : ℝ))).mdifferentiableAt
  have hH := ((((curvature_joint_contMDiff F c hc) (x, (t : ℝ)) hmem).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)).mdifferentiableAt (by simp)).comp x hspace
  have hgamma := (hc.spatial_regular t (Ioo_subset_Icc_self t.property) x).mdifferentiableAt
    (by norm_num)
  have hbase := G.covariantAlong_space_slice t hgamma hH
  obtain ⟨R, hR⟩ := (M04.isSmoothCovariantTensor_ricciEvaluation D).1 p
  have hRic : v⁻¹ * D.ricci p X H = D.ricci p S H := by
    have h := R.cons_smul ![H] v⁻¹ X
    change R ![v⁻¹ • X, H] = v⁻¹ * R ![X, H] at h
    rw [← hR, ← hR] at h
    exact h.symm
  have hA : C.split q Ahat = (A, D.ricci p S H) := by
    change C.split q (v⁻¹ • G.covariantAlong
      (fun y => G.liftCurve c (y, t)) (m62LiftedCurvature G c t) x) = _
    rw [map_smul]
    erw [hbase]
    apply Prod.ext
    · rfl
    · exact hRic
  have hS : C.split q Shat = (S, 0) :=
    (C.split q).apply_symm_apply (S, 0)
  have hdot : G.metric.inner q Ahat Shat = g.inner p A S := by
    rw [G.metric_eq, hA, hS]
    simp [q, g, p, SpacetimeData.liftCurve]
  have hP : C.split q (m62SpacetimeNormalDerivative G c t x) =
      (m62SpatialNormalDerivative F c t x, D.ricci p S H) := by
    change C.split q (Ahat - G.metric.inner q Ahat Shat • Shat) = _
    rw [map_sub, hA, map_smul, hS, hdot]
    ext <;> simp [m62SpatialNormalDerivative, A, S, g, p]
  rw [G.metric_eq, hP, pow_two]
  rfl

theorem regularized_gradient_le {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (t : OpenTime a b) (x : ℝ) :
    (m62ArcDerivative F c t (m62RegularizedCurvature F c epsilon t) x) ^ 2 ≤
      G.metric.inner (G.liftCurve c (x, t)) (m62SpacetimeNormalDerivative G c t x)
        (m62SpacetimeNormalDerivative G c t x) := by
  rw [G.normal_norm c hc t x]
  exact (PoincareConjecture.M62.regularized_gradient_le F c hc hepsilon t.property x).trans
    (le_add_of_nonneg_right (sq_nonneg _))

theorem spacetimeEvolutionRhs_eq_spatial {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c)
    (t : OpenTime a b) (x : ℝ) :
    m62SpacetimeEvolutionRhs G c t x = m62SpatialEvolutionRhs F c t x := by
  let := G.charts.chartedSpace
  let q := G.liftCurve c (x, t)
  let p := c x t
  let D := F.connection t
  let H := m62CurvatureVector F c t x
  let S := spatialUnitTangent F c t x
  let Hhat := G.charts.horizontal q H
  let Shat := G.charts.horizontal q S
  let T := G.charts.timeVector q
  obtain ⟨R, hR⟩ := (M04.isSmoothCovariantTensor_riemannEvaluation G.connection).1 q
  have hadd : G.connection.curvatureTensor q (Hhat + T) Shat Hhat Shat =
      G.connection.curvatureTensor q Hhat Shat Hhat Shat +
        G.connection.curvatureTensor q T Shat Hhat Shat := by
    have h := R.cons_add ![Shat, Hhat, Shat] Hhat T
    change R ![Hhat + T, Shat, Hhat, Shat] =
      R ![Hhat, Shat, Hhat, Shat] + R ![T, Shat, Hhat, Shat] at h
    rw [← hR, ← hR, ← hR] at h
    exact h
  have hcurv : G.connection.curvatureTensor q (G.liftedTimeVelocity c (x, t))
      (m62LiftedUnitTangent G c t x) (m62LiftedCurvature G c t x)
      (m62LiftedUnitTangent G c t x) =
      D.curvatureTensor p H S H S - D.ricci p S S * D.ricci p H H +
        (D.ricci p S H) ^ 2 +
        D.covariantTensorDerivative D.ricciEvaluation p ![H, S, S] -
        D.covariantTensorDerivative D.ricciEvaluation p ![S, S, H] := by
    rw [G.lifted_time c hc t x]
    change G.connection.curvatureTensor q (Hhat + T) Shat Hhat Shat = _
    rw [hadd, G.gauss, G.codazzi]
    change D.curvatureTensor p H S H S - D.ricci p S S * D.ricci p H H +
      D.ricci p H S * D.ricci p S H +
      (D.covariantTensorDerivative D.ricciEvaluation p ![H, S, S] -
        D.covariantTensorDerivative D.ricciEvaluation p ![S, S, H]) = _
    rw [M04.ricci_symm D p H S]
    ring
  unfold m62SpacetimeEvolutionRhs m62SpatialEvolutionRhs
  dsimp only
  rw [G.normal_norm c hc t x, hcurv]
  ring

end PoincareConjecture.M62.SpacetimeData
