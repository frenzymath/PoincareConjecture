import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundActualScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundFourJets
import PoincareConjecture.Proofs.M45.Ch9_Models.NeckBounds
import PoincareConjecture.Proofs.M36.CurvatureTrace
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveLocalIsometry
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_4_RegularRegion










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open M44

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem round_metric_error_sectional_half {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : E) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hcurv : D.curvatureTensorNorm x ≤ 9)
    (hgram : ∀ u v : E, D.curvatureTensor x u v u v =
      g.inner x u u * g.inner x v v - g.inner x u v ^ 2)
    (herror : ∀ j ≤ 2,
      g.tensorNorm (D.iteratedCovariantTensorDerivative (metricError g h) j) x ≤ epsilon)
    (u v : E) (huv : LeviCivitaData.IsOrthonormalPair h x u v) :
    (1 / 2 : ℝ) ≤ D'.sectionalCurvature x u v := by
  have hmetric (u v : E) : |h.inner x u v - g.inner x u v| ≤
      epsilon * (g.tangentNorm x u * g.tangentNorm x v) := by
    simpa! only [Nat.add_zero, LeviCivitaData.iteratedCovariantTensorDerivative, metricError,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      metricError_jet_evaluation_le D 0 x (herror 0 (by omega)) ![u, v]
  have hquad (v : E) : g.tangentNorm x v ^ 2 = g.inner x v v := by
    apply Real.sq_sqrt
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hplane (u v : E) : |D'.curvatureTensor x u v u v -
      (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)| ≤
        13 * epsilon * (g.inner x u u * g.inner x v v) := by
    have hh := abs_curvatureTensor_difference_le D D' x hepsilon
      (show epsilon ≤ 1 / 4 by linarith) hcurv herror u v u v
    rw [hgram] at hh
    have hp : g.tangentNorm x u * g.tangentNorm x v *
        g.tangentNorm x u * g.tangentNorm x v = g.inner x u u * g.inner x v v := by
      rw [← hquad, ← hquad]
      ring
    rw [hp] at hh
    have hcoeff : (9 + 3 : ℝ) * epsilon + 10 * epsilon ^ 2 ≤ 13 * epsilon := by
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (by
      rw [← hquad, ← hquad]
      positivity))
  exact sectional_half_le_of_round_plane_error D' x hepsilon hsmall hmetric hplane u v huv



theorem positive_sectional_of_rescaled_positive
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    (x : E)
    (hpositive : ∀ u v : E,
      LeviCivitaData.IsOrthonormalPair (m01RescaledMetric g Q hQ) x u v →
      0 < (m01RescaledMetric_connection g D Q hQ).sectionalCurvature x u v) :
    ∀ u v : E, LeviCivitaData.IsOrthonormalPair g x u v →
      0 < D.sectionalCurvature x u v := by
  intro u v huv
  let a := (Real.sqrt Q)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hQ).ne'
  have hfactor : a * a * Q = 1 := by
    rw [show a * a = Q⁻¹ from M13.inv_sqrt_mul_inv_sqrt Q hQ.le,
      inv_mul_cancel₀ hQ.ne']
  have hinner (v w : E) :
      (m01RescaledMetric g Q hQ).inner x (a • v) (a • w) = g.inner x v w := by
    rw [m01RescaledMetric_inner]
    simp only [map_smul, smul_apply, smul_eq_mul]
    calc
      Q * (a * (a * g.inner x v w)) = (a * a * Q) * g.inner x v w := by ring
      _ = _ := by rw [hfactor, one_mul]
  have hpair : LeviCivitaData.IsOrthonormalPair (m01RescaledMetric g Q hQ) x
      (a • u) (a • v) := by
    simpa only [LeviCivitaData.IsOrthonormalPair, hinner] using huv
  have hp := hpositive _ _ hpair
  rw [M36.sectionalCurvature_smul_pair _ x u v ha ha] at hp
  have hscale : (m01RescaledMetric_connection g D Q hQ).sectionalCurvature x u v =
      D.sectionalCurvature x u v / Q := by
    simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using
      M13.homothety_sectionalCurvature_eq g (m01RescaledMetric g Q hQ)
        (Diffeomorph.refl (𝓡 3) E ∞) Q hQ (rescaledMetric_identity_homothety hQ)
        D (m01RescaledMetric_connection g D Q hQ) x u v
  rw [hscale] at hp
  exact (div_pos_iff_of_pos_right hQ).mp hp



theorem round_component_positive
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (hsmall : epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) :
    ∀ u v : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x u v →
      0 < D.sectionalCurvature x u v := by
  obtain ⟨B, _, hB⟩ := exists_round_comparison_coordinate_bounds
  obtain ⟨_, horder⟩ := M45.model_four_jet_order N.epsilon_pos hsmall
  obtain ⟨f, V, gB, DB, hfzero, hV, hzeroV, hf, hinv, hcurv, hgram, hactual⟩ :=
    hB N (by linarith) horder (N.inverse x)
  have hfzero' : f 0 = x := hfzero.trans (N.right_inverse hx)
  obtain ⟨gE, DE, W, hW, hzeroW, hWV, hmetric⟩ :=
    M45.model_metric_realization g hV hzeroV hf hinv
  let gQ := m01RescaledMetric gE N.scale N.scale_pos
  let DQ := m01RescaledMetric_connection gE DE N.scale N.scale_pos
  have hcoeff : gQ.euclideanCoefficients =ᶠ[𝓝 0]
      (fun y => N.scale • g.pullbackCoefficients f y) := by
    filter_upwards [hW.mem_nhds hzeroW] with y hy
    exact congrArg (fun B => N.scale • B) (hmetric y hy)
  obtain ⟨_, _, herror⟩ := hactual gQ hcoeff
  have hpositiveQ : ∀ u v : E, LeviCivitaData.IsOrthonormalPair gQ 0 u v →
      0 < DQ.sectionalCurvature 0 u v := by
    intro u v huv
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      (round_metric_error_sectional_half DB DQ 0 N.epsilon_pos.le hsmall hcurv hgram
        (fun j hj => herror j (by omega)) u v huv)
  have hpositiveE := positive_sectional_of_rescaled_positive gE DE N.scale_pos 0 hpositiveQ
  have hgeom (y : E) (hy : y ∈ W) (v w : E) :
      gE.inner y v w = g.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun B => B v w) (hmetric y hy)
  have hp := (sectional_positive_iff_of_local_isometry DE D hW (hf.mono hWV)
    hgeom hzeroW).mp hpositiveE
  exact hfzero' ▸ hp



theorem canonical_neck_or_cap_of_not_positive
    {F : SurgeryFlowData.{u}} {t : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x) :
    (∃ N : SurgeryStrongNeck F t F.parameters.epsilon, N.neck.center = x) ∨
    ∃ N : CapCertificate (F.metric t), N.epsilon = F.parameters.epsilon ∧
      N.cap_constant ≤ F.parameters.C ∧ N.connection = F.connection t ∧ x ∈ N.core := by
  cases hcanonical with
  | neck N hx => exact Or.inl ⟨N, hx⟩
  | cap N he hC hD hx => exact Or.inr ⟨N, he, hC, hD, hx⟩
  | component N hx =>
      have hxcomponent : x ∈ connectedComponent N.basepoint := by rwa [← N.component_eq]
      have hcomponent : connectedComponent x = N.carrier :=
        (connectedComponent_eq hxcomponent).symm.trans N.component_eq.symm
      exact (hpositive (fun y hy => N.positive_sectional y (hcomponent ▸ hy))).elim
  | round N hx =>
      have hxcomponent : x ∈ connectedComponent N.basepoint := by rwa [← N.component_eq]
      have hcomponent : connectedComponent x = N.carrier :=
        (connectedComponent_eq hxcomponent).symm.trans N.component_eq.symm
      exact (hpositive (fun y hy => round_component_positive (F.metric t) (F.connection t)
        N F.parameters.epsilon_le (hcomponent ▸ hy))).elim

end PoincareConjecture.Proofs.M46
