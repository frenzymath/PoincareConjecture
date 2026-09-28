import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Convergence

set_option autoImplicit false
set_option maxSynthPendingDepth 5
open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

namespace PoincareConjecture

private theorem differentiableAt_of_section {n : ℕ}
    {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (Y y)) x) :
    DifferentiableAt ℝ Y x := by
  rw [mdifferentiableAt_totalSpace] at hY
  simpa using mdifferentiableAt_iff_differentiableAt.mp hY.2

set_option backward.isDefEq.respectTransparency false in
private theorem flat_isCovariantDerivativeOn (n : ℕ) :
    IsCovariantDerivativeOn (EuclideanSpace ℝ (Fin n))
      (I := 𝓡 n) (V := TangentSpace (𝓡 n))
      (fun Y x => fderiv ℝ Y x) univ := by
  constructor
  · intro Y Z x hY hZ hx
    exact fderiv_add (differentiableAt_of_section hY) (differentiableAt_of_section hZ)
  · intro Y f x hY hf hx
    have h := fderiv_smul (mdifferentiableAt_iff_differentiableAt.mp hf)
      (differentiableAt_of_section hY)
    ext v
    have hh := congrArg (fun L => L v) h
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply] at hh
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    convert! hh using 1

private theorem extend_eq_const {n : ℕ} (x v y : EuclideanSpace ℝ (Fin n)) :
    FiberBundle.extend (EuclideanSpace ℝ (Fin n))
      (E := TangentSpace (𝓡 n)) (x := x) v y = v := by
  simp only [FiberBundle.extend, trivializationAt_model_space_apply]
  have h := (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL_apply
    (R := ℝ) (b := y) (by change y ∈ univ; trivial) (y := v)
  simp only [TangentBundle.symmL_model_space] at h
  exact h.symm

namespace LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem connection_eq_fderiv_add (D : LeviCivitaData g)
    {Y : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hY : DifferentiableAt ℝ Y x)
    (v : EuclideanSpace ℝ (Fin n)) :
    D.connection Y x v = fderiv ℝ Y x v + D.euclideanConnection v (Y x) x := by
  have hy : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (Y y)) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using mdifferentiableAt_iff_differentiableAt.mpr hY⟩
  have hc : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (Y x)) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using mdifferentiableAt_const (c := Y x)⟩
  have h₁ := D.connection.isCovariantDerivativeOnUniv.difference_apply
    (flat_isCovariantDerivativeOn n) (by simp) hy
  have h₂ := D.connection.isCovariantDerivativeOnUniv.difference_apply
    (flat_isCovariantDerivativeOn n) (by simp) hc
  have h := congrArg (fun L => L v) (h₁.symm.trans h₂)
  let a : EuclideanSpace ℝ (Fin n) := D.connection Y x v
  let b : EuclideanSpace ℝ (Fin n) := D.euclideanConnection v (Y x) x
  change a - fderiv ℝ Y x v = b - fderiv ℝ (fun _ => Y x) x v at h
  simp only [fderiv_const_apply, zero_apply, sub_zero] at h
  convert! (sub_eq_iff_eq_add.mp h).trans (add_comm _ _) using 1

theorem contDiffAt_euclideanConnection (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (D.euclideanConnection u v) x := by
  have hc (w : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
          (E := TangentSpace (𝓡 n)) w) x := by
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := w)⟩
  have h := D.contMDiffAt_covariantDerivativeOnFields (hc u) (hc v)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp at hh
  convert! contMDiffAt_iff_contDiffAt.mp hh using 1

set_option backward.isDefEq.respectTransparency false in

theorem curvature_eq_euclideanConnection (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    D.curvature x u v w =
      fderiv ℝ (D.euclideanConnection v w) x u +
        D.euclideanConnection u (D.euclideanConnection v w x) x -
      (fderiv ℝ (D.euclideanConnection u w) x v +
        D.euclideanConnection v (D.euclideanConnection u w x) x) := by
  have he (a : EuclideanSpace ℝ (Fin n)) :
      FiberBundle.extend (EuclideanSpace ℝ (Fin n))
        (E := TangentSpace (𝓡 n)) (x := x) a = fun _ => a :=
    funext (extend_eq_const x a)
  unfold curvature
  rw [he, he, he]
  unfold curvatureOnFields
  have hb : mlieBracket (𝓡 n) (fun _ : EuclideanSpace ℝ (Fin n) => u)
      (fun _ => v) x = 0 := by
    simp only [mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ, fderiv_const_apply, zero_apply, sub_self]
  rw [hb, map_zero, sub_zero]
  change D.connection (D.euclideanConnection v w) x u -
      D.connection (D.euclideanConnection u w) x v = _
  rw [D.connection_eq_fderiv_add
      ((D.contDiffAt_euclideanConnection x v w).differentiableAt (by simp)),
    D.connection_eq_fderiv_add
      ((D.contDiffAt_euclideanConnection x u w).differentiableAt (by simp))]

private theorem tendsto_euclideanConnection_of_metric_jets
    {ι : Type*} {l : Filter ι}
    {gseq : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x u : EuclideanSpace ℝ (Fin n))
    {vseq : ι → EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin n)}
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (hv : Tendsto vseq l (𝓝 v)) :
    Tendsto (fun i => (Dseq i).euclideanConnection u (vseq i) x) l
      (𝓝 (D.euclideanConnection u v x)) := by
  let V := EuclideanSpace ℝ (Fin n)
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hi := (hginv.contDiffAt_map_inverse (n := 0)).continuousAt.tendsto.comp hzero
  have hk : Continuous (fun p : (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) × V =>
      metricKoszulCovector p.1 u p.2) := by
    have hf : Continuous (fun B : V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).continuous
    have hf' : Continuous (fun B : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => B.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ V V (V →L[ℝ] ℝ)).continuous
    unfold metricKoszulCovector
    fun_prop
  have hK := hk.continuousAt.tendsto.comp (hone.prodMk_nhds hv)
  simp_rw [euclideanConnection, connection_const_eq_inverse]
  convert!
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hi.prodMk_nhds hK) using 1

theorem tendsto_curvature_of_metric_jets
    {ι : Type*} {l : Filter ι}
    {gseq : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun i => (Dseq i).curvature x u v w) l (𝓝 (D.curvature x u v w)) := by
  have hc a b := tendsto_connection_const_of_metric_jets Dseq D x a b hzero hone
  have hd a b (c : EuclideanSpace ℝ (Fin n)) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      ((tendsto_fderiv_connection_const_of_metric_jets Dseq D x a b
        hzero hone htwo).prodMk_nhds (tendsto_const_nhds (x := c)))
  have hn a b c := tendsto_euclideanConnection_of_metric_jets Dseq D x a
    hzero hone (hc b c)
  simp_rw [curvature_eq_euclideanConnection]
  convert! ((hd v w u).add (hn u v w)).sub ((hd u w v).add (hn v u w)) using 1

theorem tendsto_curvatureTensor_of_metric_jets
    {ι : Type*} {l : Filter ι}
    {gseq : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (x u v w z : EuclideanSpace ℝ (Fin n))
    (hzero : Tendsto (fun i => (gseq i).euclideanCoefficients x) l
      (𝓝 (g.euclideanCoefficients x)))
    (hone : Tendsto (fun i => fderiv ℝ (gseq i).euclideanCoefficients x) l
      (𝓝 (fderiv ℝ g.euclideanCoefficients x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (gseq i).euclideanCoefficients) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x))) :
    Tendsto (fun i => (Dseq i).curvatureTensor x u v w z) l
      (𝓝 (D.curvatureTensor x u v w z)) := by
  have hc := tendsto_curvature_of_metric_jets Dseq D x u v z hzero hone htwo
  have hp := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hzero.prodMk_nhds hc)
  convert! (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hp.prodMk_nhds (tendsto_const_nhds (x := w))) using 1

end LeviCivitaData
end PoincareConjecture
