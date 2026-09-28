import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetSpatialCalculus











set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62 Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63HasDerivAt_tensor_pullback {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (hT : IsSmoothCovariantTensor T) {gamma : ℝ → M} {x : ℝ}
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma x)
    (Y : Fin k → (s : ℝ) → TangentSpace (𝓡 n) (gamma s))
    (hY : ∀ i, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, Y i s⟩ : TangentBundle (𝓡 n) M)) x) :
    HasDerivAt (fun s => T (gamma s) (fun i => Y i s))
      (D.covariantTensorDerivative T (gamma x)
        (Fin.cons (curveVelocity gamma x) (fun i => Y i x)) +
        ∑ i, T (gamma x) (Function.update (fun j => Y j x) i
          (rampHorizontalCovariantDerivative D gamma (Y i) x))) x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let p := gamma x
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let y : Fin k → ℝ → EuclideanSpace ℝ (Fin n) :=
    fun i s => (e ⟨gamma s, Y i s⟩).2
  let v : Fin k → ℝ → TangentSpace (𝓡 n) p :=
    fun i s => e.symmL ℝ p (y i s)
  have hy (i : Fin k) : DifferentiableAt ℝ (y i) x := by
    have h := hY i
    rw [mdifferentiableAt_totalSpace] at h
    exact h.2.differentiableAt
  have hv (i : Fin k) : HasDerivAt (v i) (e.symmL ℝ p (deriv (y i) x)) x :=
    (e.symmL ℝ p).hasFDerivAt.comp_hasDerivAt x (hy i).hasDerivAt
  have hvx (i : Fin k) : v i x = Y i x := by
    change e.symmL ℝ p (e ⟨p, Y i x⟩).2 = Y i x
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hp]
    exact e.symmL_continuousLinearMapAt hp _
  let A : ℝ → TensorFiber (TangentSpace (𝓡 n) p) k := fun s =>
    TensorFiber.toMultilinear.symm ((hT.1 (gamma s)).choose.compLinearMap
      (fun _ => (extensionMap p (gamma s)).toLinearMap))
  have hAeval (s : ℝ) (w : Fin k → TangentSpace (𝓡 n) p) :
      A s w = T (gamma s) (fun i => extensionMap p (gamma s) (w i)) :=
    ((hT.1 (gamma s)).choose_spec _).symm
  have hAself (w : Fin k → TangentSpace (𝓡 n) p) : A x w = T p w := by
    rw [hAeval]
    change T p (fun i => extensionMap p p (w i)) = T p w
    simp only [extensionMap_self, ContinuousLinearMap.id_apply]
  have hfield (w : Fin k → TangentSpace (𝓡 n) p) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun q => T q (fun i => extensionMap p q (w i))) p :=
    (hT.2 e.baseSet e.open_baseSet (fun i q => extensionMap p q (w i))
      (fun i => extensionMap_smooth p (w i))).contMDiffAt (e.open_baseSet.mem_nhds hp)
  have hAsmooth : ContDiffAt ℝ ∞ A x := by
    apply TensorFiber.contDiffAt_of_evaluation
    intro w
    simpa only [hAeval, Function.comp_def] using ((hfield w).comp x hgamma).contDiffAt
  have hAdiff := hAsmooth.differentiableAt (by simp)
  have hDA (w : Fin k → TangentSpace (𝓡 n) p) :
      (fderiv ℝ A x 1) w =
        D.covariantTensorDerivative T p (Fin.cons (curveVelocity gamma x) w) +
          ∑ i, T p (Function.update w i
            (frozenConnectionEndomorphism D p (curveVelocity gamma x) (w i))) := by
    have hchain : HasDerivAt
        (fun s => T (gamma s) (fun i => extensionMap p (gamma s) (w i)))
        (mvfderiv (𝓡 n) (fun q => T q (fun i => extensionMap p q (w i)))
          p (curveVelocity gamma x)) x := by
      have hsmooth : ContDiffAt ℝ ∞
          (fun s => T (gamma s) (fun i => extensionMap p (gamma s) (w i))) x := by
        simpa only [Function.comp_def] using ((hfield w).comp x hgamma).contDiffAt
      apply ((hsmooth.differentiableAt (by simp)).hasDerivAt).congr_deriv
      have hcomp := mvfderiv_comp_apply x ((hfield w).mdifferentiableAt (by simp))
        (hgamma.mdifferentiableAt (by simp)) (1 : ℝ)
      simpa only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
        ContinuousLinearMap.comp_apply, Function.comp_def, curveVelocity, p,
        fderiv_apply_one_eq_deriv] using! hcomp
    have hchainA : HasDerivAt (fun s => A s w)
        (mvfderiv (𝓡 n) (fun q => T q (fun i => extensionMap p q (w i)))
          p (curveVelocity gamma x)) x :=
      hchain.congr_of_eventuallyEq (Eventually.of_forall fun s => hAeval s w)
    calc
      (fderiv ℝ A x 1) w = fderiv ℝ (fun s => A s w) x 1 :=
        (TensorFiber.fderiv_evaluation hAdiff w (1 : ℝ)).symm
      _ = deriv (fun s => A s w) x := rfl
      _ = _ := hchainA.deriv
      _ = _ := extensionTensor_derivative D T p (curveVelocity gamma x) w
  have hC := (TensorFiber.continuousMultilinear
    (E := TangentSpace (𝓡 n) p) (k := k)).hasFDerivAt.comp x hAdiff.hasFDerivAt
  have hprodDiff : DifferentiableAt ℝ (fun s => A s (fun i => v i s)) x :=
    (hC.continuousMultilinearMap_apply (fun i => (hv i).hasFDerivAt)).differentiableAt
  have hprod := TensorFiber.fderiv_apply hAdiff (fun i => (hv i).differentiableAt) (1 : ℝ)
  rw [hDA] at hprod
  have hderv (i : Fin k) : deriv (v i) x = e.symmL ℝ p (deriv (y i) x) := (hv i).deriv
  simp only [fderiv_apply_one_eq_deriv, hderv, hAself, hvx] at hprod
  have hnear : ∀ᶠ s in 𝓝 x, gamma s ∈ e.baseSet :=
    hgamma.continuousAt (e.open_baseSet.mem_nhds hp)
  have hrep (s : ℝ) (hs : gamma s ∈ e.baseSet) (i : Fin k) :
      extensionMap p (gamma s) (v i s) = Y i s := by
    change e.symmL ℝ (gamma s)
      (e.continuousLinearMapAt ℝ p (e.symmL ℝ p (e ⟨gamma s, Y i s⟩).2)) = Y i s
    rw [e.continuousLinearMapAt_symmL hp,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hs]
    exact e.symmL_continuousLinearMapAt hs _
  have heq : (fun s => T (gamma s) (fun i => Y i s)) =ᶠ[𝓝 x]
      (fun s => A s (fun i => v i s)) := by
    filter_upwards [hnear] with s hs
    rw [hAeval]
    simp only [hrep s hs]
  have hslot (i : Fin k) :
      T p (Function.update (fun j => Y j x) i
        (rampHorizontalCovariantDerivative D gamma (Y i) x)) =
      T p (Function.update (fun j => Y j x) i (e.symmL ℝ p (deriv (y i) x))) +
        T p (Function.update (fun j => Y j x) i
          (frozenConnectionEndomorphism D p (curveVelocity gamma x) (Y i x))) := by
    obtain ⟨L, hL⟩ := hT.1 p
    change T p (Function.update (fun j => Y j x) i
      (e.symmL ℝ p (deriv (y i) x) +
        frozenConnectionEndomorphism D p (curveVelocity gamma x) (Y i x))) = _
    simp only [hL, L.map_update_add]
  apply (hprodDiff.hasDerivAt.congr_of_eventuallyEq heq).congr_deriv
  change deriv (fun s => A s (fun i => v i s)) x =
    D.covariantTensorDerivative T p (Fin.cons (curveVelocity gamma x) (fun i => Y i x)) +
      ∑ i, T p (Function.update (fun j => Y j x) i
        (rampHorizontalCovariantDerivative D gamma (Y i) x))
  rw [hprod]
  simp_rw [hslot]
  rw [Finset.sum_add_distrib]
  ring




theorem m63ArcDerivative_tensor_pullback
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (hT : IsSmoothCovariantTensor T)
    (Y : Fin k → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    m62ArcDerivative F c t (fun y => T (c y t) (fun i => Y i (y, t))) x =
      (F.connection t).covariantTensorDerivative T (c x t)
        (Fin.cons (spatialUnitTangent F c t x) (fun i => Y i (x, t))) +
        ∑ i, T (c x t) (Function.update (fun j => Y j (x, t)) i
          (m62SpatialDerivative F c t (fun y => Y i (y, t)) x)) := by
  classical
  let D := F.connection t
  let p := c x t
  let theta := (curveSpeed F c t x)⁻¹
  let X := curveVelocity (n := n) (fun y => c y t) x
  let S := spatialUnitTangent F c t x
  let V := fun i => Y i (x, t)
  let W := fun i => rampHorizontalCovariantDerivative D (fun y => c y t)
    (fun y => Y i (y, t)) x
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : ℝ => (y, t)) x :=
    (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x hs
  have hYs (i : Fin k) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, Y i (y, t)⟩ : TangentBundle (𝓡 n) M)) x :=
    (((hY i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt (by simp)
  have hraw := m63HasDerivAt_tensor_pullback D T hT hcurve
    (fun i y => Y i (y, t)) hYs
  obtain ⟨L, hL⟩ := hT.1 p
  have hslot (i : Fin k) :
      T p (Function.update V i (m62SpatialDerivative F c t (fun y => Y i (y, t)) x)) =
        theta * T p (Function.update V i (W i)) := by
    change T p (Function.update V i (theta • W i)) = theta * T p (Function.update V i (W i))
    simpa only [← hL, smul_eq_mul] using L.map_update_smul V i theta (W i)
  obtain ⟨L', hL'⟩ := (M04.isSmoothCovariantTensor_covariantTensorDerivative D hT).1 p
  have hlead : D.covariantTensorDerivative T p (Fin.cons S V) =
      theta * D.covariantTensorDerivative T p (Fin.cons X V) := by
    change D.covariantTensorDerivative T p (Fin.cons (theta • X) V) = _
    simpa only [Fin.update_cons_zero, ← hL', smul_eq_mul] using
      L'.map_update_smul (Fin.cons X V) 0 theta X
  rw [m62ArcDerivative, hraw.deriv]
  change theta * (D.covariantTensorDerivative T p (Fin.cons X V) +
      ∑ i, T p (Function.update V i (W i))) =
    D.covariantTensorDerivative T p (Fin.cons S V) +
      ∑ i, T p (Function.update V i (m62SpatialDerivative F c t (fun y => Y i (y, t)) x))
  rw [hlead]
  simp_rw [hslot]
  rw [mul_add, Finset.mul_sum]

end PoincareConjecture
