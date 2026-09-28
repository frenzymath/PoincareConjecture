import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Topology

open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def extensionMap (p q : M) :
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) q :=
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
  (e.symmL ℝ q).comp (e.continuousLinearMapAt ℝ p)

theorem extensionMap_apply (p q : M)
    (hq : q ∈ (trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p).baseSet)
    (v : TangentSpace (𝓡 n) p) :
    extensionMap p q v = FiberBundle.extend E v q := by
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  change e.symmL ℝ q (e.continuousLinearMapAt ℝ p v) = e.symm q (e ⟨p, v⟩).2
  rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hp]
  exact e.symmL_apply hq _

theorem extensionMap_eventuallyEq (p : M) (v : TangentSpace (𝓡 n) p) :
    (fun q ↦ extensionMap p q v) =ᶠ[𝓝 p]
      FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E v := by
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p)]
    with q hq
  exact extensionMap_apply p q hq v

theorem extensionMap_self (p : M) :
    extensionMap p p = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) p) := by
  ext v
  rw [extensionMap_apply p p (FiberBundle.mem_baseSet_trivializationAt' p),
    FiberBundle.extend_apply_self]
  rfl

theorem frozenExtend_add (p : M) (v w : TangentSpace (𝓡 n) p) :
    FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E (v + w) =ᶠ[𝓝 p]
      FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E v +
        FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E w := by
  filter_upwards [extensionMap_eventuallyEq p (v + w), extensionMap_eventuallyEq p v,
    extensionMap_eventuallyEq p w] with q hvw hv hw
  simp only [Pi.add_apply, ← hvw, ← hv, ← hw, map_add]
  rfl

theorem frozenExtend_smul (p : M) (a : ℝ) (v : TangentSpace (𝓡 n) p) :
    FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E (a • v) =ᶠ[𝓝 p]
      a • FiberBundle.extend («E» := TangentSpace (𝓡 n)) (x := p) E v := by
  filter_upwards [extensionMap_eventuallyEq p (a • v), extensionMap_eventuallyEq p v]
    with q hav hv
  simp only [Pi.smul_apply, ← hav, ← hv, map_smul]
  rfl

noncomputable def extensionEquiv (p q : M)
    (hq : q ∈ (trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p).baseSet) :
    TangentSpace (𝓡 n) p ≃L[ℝ] TangentSpace (𝓡 n) q :=
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
  (e.continuousLinearEquivAt ℝ p (FiberBundle.mem_baseSet_trivializationAt' p)).trans
    (e.continuousLinearEquivAt ℝ q hq).symm

theorem extensionEquiv_coe (p q : M)
    (hq : q ∈ (trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p).baseSet) :
    (extensionEquiv p q hq : TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) q) =
      extensionMap p q := by
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
  ext v
  change (e.continuousLinearEquivAt ℝ q hq).symm
      (e.continuousLinearEquivAt ℝ p (FiberBundle.mem_baseSet_trivializationAt' p) v) = _
  rw [e.symm_continuousLinearEquivAt_eq hq,
    e.coe_continuousLinearEquivAt_eq (FiberBundle.mem_baseSet_trivializationAt' p)]
  rfl

theorem extensionMap_smooth (p : M) (v : TangentSpace (𝓡 n) p) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (fun q ↦ extensionMap p q v))
      (trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p).baseSet := by
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
  suffices ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (fun q ↦ (e ⟨q, extensionMap p q v⟩).2) e.baseSet by
    intro q hq
    rw [e.contMDiffWithinAt_section _ hq]
    exact this q hq
  have h : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (fun _ : M ↦ (e ⟨p, v⟩).2) e.baseSet :=
    contMDiffOn_const
  exact h.congr fun q hq ↦ by
    rw [extensionMap_apply p q hq]
    simp only [FiberBundle.extend]
    change (e ⟨q, e.symm q (e ⟨p, v⟩).2⟩).2 = (e ⟨p, v⟩).2
    simp [hq]

noncomputable def frozenConnectionEndomorphism {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (X : TangentSpace (𝓡 n) p) :
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace (𝓡 n) : M → Type _) p
  let L : TangentSpace (𝓡 n) p →ₗ[ℝ] TangentSpace (𝓡 n) p := {
    toFun := fun v ↦ D.connection (FiberBundle.extend E v) p X
    map_add' := by
      intro v w
      have hv := FiberBundle.mdifferentiableAt_extend (𝓡 n) E v
      have hw := FiberBundle.mdifferentiableAt_extend (𝓡 n) E w
      have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (FiberBundle.mdifferentiableAt_extend (𝓡 n) E (v + w))
        (mdifferentiableAt_add_section hv hw) (by simp) (frozenExtend_add p v w)
      rw [hc, D.connection.isCovariantDerivativeOnUniv.add hv hw]
      rfl
    map_smul' := by
      intro a v
      have hv := FiberBundle.mdifferentiableAt_extend (𝓡 n) E v
      have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
        (FiberBundle.mdifferentiableAt_extend (𝓡 n) E (a • v))
        (hv.smul_const_section (a := a)) (by simp) (frozenExtend_smul p a v)
      rw [hc, D.connection.isCovariantDerivativeOnUniv.smul_const a hv]
      rfl }
  exact L.toContinuousLinearMap

theorem frozenConnectionEndomorphism_apply {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (X v : TangentSpace (𝓡 n) p) :
    frozenConnectionEndomorphism D p X v = D.connection (FiberBundle.extend E v) p X :=
  rfl

theorem extensionMetric_derivative {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (X v w : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ g.inner q (extensionMap p q v) (extensionMap p q w)) p X =
      g.inner p (frozenConnectionEndomorphism D p X v) w +
        g.inner p v (frozenConnectionEndomorphism D p X w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.metricCompatible.mvfderiv_inner_eq (FiberBundle.extend E X)
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) E v)
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) E w)
  have heq : (fun q ↦ g.inner q (extensionMap p q v) (extensionMap p q w)) =ᶠ[𝓝 p]
      (fun q ↦ g.inner q (FiberBundle.extend E v q) (FiberBundle.extend E w q)) := by
    filter_upwards [extensionMap_eventuallyEq p v, extensionMap_eventuallyEq p w]
      with q hv hw
    rw [hv, hw]
  rw [mvfderiv, heq.mfderiv_eq]
  simpa only [FiberBundle.extend_apply_self, frozenConnectionEndomorphism_apply,
    mvfderiv] using! h

theorem extensionTensor_derivative {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (p : M) (X : TangentSpace (𝓡 n) p) (v : Fin k → TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ T q (fun i ↦ extensionMap p q (v i))) p X =
      D.covariantTensorDerivative T p (Fin.cons X v) +
        ∑ i, T p (Function.update v i (frozenConnectionEndomorphism D p X (v i))) := by
  classical
  have heq : (fun q ↦ T q (fun i ↦ extensionMap p q (v i))) =ᶠ[𝓝 p]
      (fun q ↦ T q (fun i ↦ FiberBundle.extend E (v i) q)) := by
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p
    filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p)]
      with q hq
    simp only [extensionMap_apply p q hq]
  have hraw : D.covariantTensorDerivative T p (Fin.cons X v) =
      mvfderiv (𝓡 n) (fun q ↦ T q (fun i ↦ FiberBundle.extend E (v i) q)) p X -
        ∑ i, T p (Function.update v i (frozenConnectionEndomorphism D p X (v i))) := by
    rfl
  rw [hraw, sub_add_cancel, mvfderiv, heq.mfderiv_eq]
  rfl

end PoincareConjecture.Proofs.M09
