import PoincareConjecture.Proofs.M35.Uniqueness.RadialMetricDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness


noncomputable def radialConnectionAlpha
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  deriv (axisAngularCoefficient g) r / (2 * axisAngularCoefficient g r * r)


noncomputable def radialConnectionBeta
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  (axisCorrectionCoefficient g r - deriv (axisAngularCoefficient g) r / (2 * r)) /
    axisRadialCoefficient g r


noncomputable def radialConnectionGamma
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  (deriv (axisCorrectionCoefficient g) r / (2 * r) -
    2 * axisCorrectionCoefficient g r * radialConnectionAlpha g r) /
      axisRadialCoefficient g r



theorem rotational_connection_const
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    D.connection (fun _ : StandardCapSpace => v) x u =
      radialConnectionAlpha g ‖x‖ • (inner ℝ x u • v + inner ℝ x v • u) +
      (radialConnectionBeta g ‖x‖ * inner ℝ u v +
        radialConnectionGamma g ‖x‖ * inner ℝ x u * inner ℝ x v) • x := by
  let z : StandardCapSpace :=
    radialConnectionAlpha g ‖x‖ • (inner ℝ x u • v + inner ℝ x v • u) +
      (radialConnectionBeta g ‖x‖ * inner ℝ u v +
        radialConnectionGamma g ‖x‖ * inner ℝ x u * inner ℝ x v) • x
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ha : axisAngularCoefficient g ‖x‖ ≠ 0 :=
    (axisAngularCoefficient_pos g ‖x‖).ne'
  have hb : axisRadialCoefficient g ‖x‖ ≠ 0 :=
    (axisRadialCoefficient_pos g ‖x‖).ne'
  have hpair (w : StandardCapSpace) :
      g.inner x (D.connection (fun _ : StandardCapSpace => v) x u) w = g.inner x z w := by
    have h := rotational_inner_connection_const D hrotation hx u v w
    have hz : 2 * g.inner x z w =
        deriv (axisAngularCoefficient g) ‖x‖ / ‖x‖ *
          (inner ℝ x u * inner ℝ v w + inner ℝ x v * inner ℝ u w -
            inner ℝ x w * inner ℝ u v) +
          deriv (axisCorrectionCoefficient g) ‖x‖ / ‖x‖ *
            inner ℝ x u * inner ℝ x v * inner ℝ x w +
          2 * axisCorrectionCoefficient g ‖x‖ * inner ℝ u v * inner ℝ x w := by
      rw [rotational_metric_form_correction g hrotation hx]
      simp only [z, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        real_inner_self_eq_norm_sq, conj_trivial]
      unfold radialConnectionBeta radialConnectionGamma radialConnectionAlpha
        axisCorrectionCoefficient
      field_simp [ha, hb, hn]
      ring
    linarith only [h, hz]
  let y : StandardCapSpace := D.connection (fun _ : StandardCapSpace => v) x u
  change y = z
  by_contra hne
  have hnonzero : y - z ≠ 0 :=
    sub_ne_zero.mpr hne
  have hzero : g.inner x (y - z) (y - z) = 0 := by
    change g.euclideanCoefficients x (y - z) (y - z) = 0
    calc
      _ = g.euclideanCoefficients x y (y - z) -
          g.euclideanCoefficients x z (y - z) :=
        congrArg (fun L => L (y - z)) ((g.euclideanCoefficients x).map_sub y z)
      _ = 0 := sub_eq_zero.mpr (hpair _)
  exact (ne_of_gt (g.pos x _ hnonzero)) hzero

end PoincareConjecture.M35.Uniqueness
