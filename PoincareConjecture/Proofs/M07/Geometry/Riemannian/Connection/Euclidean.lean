import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.LocalRegularity








set_option autoImplicit false
set_option maxSynthPendingDepth 5
open scoped Manifold ContDiff Topology
open Filter Set VectorField

namespace PoincareConjecture

variable {n : ℕ} {g : PoincareConjecture.RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private lemma contMDiffAt_const_field (x v : EuclideanSpace ℝ (Fin n)) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : EuclideanSpace ℝ (Fin n) => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) y (E := TangentSpace (𝓡 n)) v) x := by
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  simpa using (contMDiffAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := v) (x := x))

namespace RiemannianMetric


def euclideanCoefficients (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun y => g.inner y


theorem contDiffAt_euclideanCoefficients (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ g.euclideanCoefficients x := by
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_of_apply
  intro u
  apply contMDiffAt_clm_of_apply
  intro v
  have h := ((g.contMDiff x).clm_bundle_apply (contMDiffAt_const_field x u)).clm_bundle_apply
    (contMDiffAt_const_field x v)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp at hh
  convert! hh using 1

end RiemannianMetric


noncomputable def metricKoszulCovector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) (u v : V) : V →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (B u v + (B v).flip u - (B.flip u).flip v)

theorem continuous_metricKoszulCovector
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (u v : V) :
    Continuous (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => metricKoszulCovector B u v) := by
  have hf : Continuous (fun B : V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous
  have hf' : Continuous (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V (V →L[ℝ] ℝ)).continuous
  unfold metricKoszulCovector
  fun_prop

namespace LeviCivitaData

set_option backward.isDefEq.respectTransparency false in

theorem inner_connection_const (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    2 * g.inner x (D.connection (fun _ : EuclideanSpace ℝ (Fin n) => v) x u) w =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g.inner y v w) x u +
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g.inner y w u) x v -
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g.inner y u v) x w := by
  have h := D.koszul_identity
    ((contMDiffAt_const_field x u).mdifferentiableAt (by simp))
    ((contMDiffAt_const_field x v).mdifferentiableAt (by simp))
    ((contMDiffAt_const_field x w).mdifferentiableAt (by simp))
  simp only [covariantDerivativeOnFields, mvfderiv, mfderiv_eq_fderiv,
    mlieBracket, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin,
    fderivWithin_univ, fderiv_const_apply] at h
  simp +instances [NormedSpace.fromTangentSpace] at h
  convert! h using 2

set_option backward.isDefEq.respectTransparency false in


theorem connection_const_eq_inverse (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.connection (fun _ : EuclideanSpace ℝ (Fin n) => v) x u =
      (g.euclideanCoefficients x).inverse
        (metricKoszulCovector (V := EuclideanSpace ℝ (Fin n))
          (fderiv ℝ g.euclideanCoefficients x)
          u v) := by
  symm
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  apply hginv.inverse_apply_eq.mpr
  ext w
  have hd (a b c : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => g.inner y a b) x c =
        (fderiv ℝ g.euclideanCoefficients x c) a b := by
    have hG := ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)).hasFDerivAt
    have h := (hG.clm_apply (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
    have hh := congrArg (fun L => L c) h.fderiv
    simp at hh
    convert! hh using 1
  have h := D.inner_connection_const x u v w
  rw [hd, hd, hd] at h
  simp only [metricKoszulCovector, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, RiemannianMetric.euclideanCoefficients]
  have hh := congrArg (fun a : ℝ => (2⁻¹ : ℝ) * a) h.symm
  simp only [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul] at hh
  convert! hh using 1



theorem tendsto_connection_const_of_metric_jets
    {ι : Type*} {l : Filter ι}
    {gseq : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x))) :
    Tendsto (fun i => (Dseq i).connection (fun _ : EuclideanSpace ℝ (Fin n) => v) x u) l
      (𝓝 (D.connection (fun _ : EuclideanSpace ℝ (Fin n) => v) x u)) := by
  simp_rw [connection_const_eq_inverse]
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hi := (hginv.contDiffAt_map_inverse (n := 0)).continuousAt.tendsto.comp hzero
  have hc := (continuous_metricKoszulCovector u v).tendsto _ |>.comp hone
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hi.prodMk_nhds hc)

end LeviCivitaData
end PoincareConjecture
