import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Matrix
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricDuality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.DerivativeOnFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma eventually_exists_basis_extend {ι : Type} (x : M)
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    ∀ᶠ y in nhds x, ∃ c : Module.Basis ι ℝ (TangentSpace (𝓡 n) y),
      ∀ i, c i = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V x
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  let L := (e.continuousLinearEquivAt ℝ x hx).trans
    (e.continuousLinearEquivAt ℝ y hy).symm
  refine ⟨b.map L.toLinearEquiv, fun i => ?_⟩
  change (e.continuousLinearEquivAt ℝ y hy).symm
    ((e.continuousLinearEquivAt ℝ x hx) (b i)) = _
  rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq,
    Bundle.Trivialization.symmL_apply _ hy]
  rfl

lemma contMDiffAt_tensor_update_connection_fields
    (F : RicciFlow n M J) {k : ℕ} {T : ℝ → CovariantTensorEvaluation n M k}
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ X : Fin k → (y : M) → TangentSpace (𝓡 n) y,
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) x) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, x))
    {X : Fin k → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x)
    {U V : (y : M) → TangentSpace (𝓡 n) y}
    (hU : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% U) x)
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) x)
    (r : Fin k) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => T p.1 p.2 (Function.update (fun i => X i p.2) r
        ((F.connection p.1).connection V p.2 (U p.2)))) (t, x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let b := (F.metric t).orthonormalBasis x
  let e := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G : ℝ × M → Matrix _ _ ℝ := fun p i j =>
    (F.metric p.1).inner p.2 (e i p.2) (e j p.2)
  have he (i) : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (e i)) x := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) _ (b i)
  have hG (i j) := F.contMDiffAt_inner_fields ht (he i) (he j)
  have hGx : G (t, x) = 1 := by
    ext i j
    change (F.metric t).inner x (e i x) (e j x) = _
    simp only [e, FiberBundle.extend_apply_self]
    exact b.inner_eq_ite i j
  have hi := Poincare.Manifold.contMDiffAt_matrix_inv_entry G (t, x) hG (by simp [hGx])
  have hA (j) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => T p.1 p.2 (Function.update (fun i => X i p.2) r (e j p.2)))
      (t, x) := by
    have h := hreg (Function.update X r (e j)) (fun a => by
      by_cases ha : a = r
      · subst a; simpa using he j
      · simpa [Function.update_of_ne ha] using hX a)
    convert h using 1
    funext p
    congr 1
    ext a
    by_cases ha : a = r <;> simp [ha]
  have hC (i) := F.contMDiffAt_inner_connection_fields ht hU hV (he i)
  have hsum := ContMDiffAt.sum (t := Finset.univ) fun i _ =>
    ContMDiffAt.sum (t := Finset.univ) fun j _ => (hi i j).mul ((hC i).mul (hA j))
  apply hsum.congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually (eventually_exists_basis_extend x b.toBasis)] with p hp
  obtain ⟨c, hc⟩ := hp
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric p.1).toRiemannianMetric⟩
  obtain ⟨B, hB⟩ := (hT p.1).1 p.2
  have h := linear_apply_eq_inverse_gram (B.toLinearMap (fun i => X i p.2) r)
    ((F.connection p.1).connection V p.2 (U p.2)) c ((F.metric p.1).orthonormalBasis p.2)
  change B (Function.update (fun i => X i p.2) r
    ((F.connection p.1).connection V p.2 (U p.2))) =
    ∑ i, ∑ j, (Matrix.of (fun i j => (F.metric p.1).inner p.2 (c i) (c j)))⁻¹ i j *
      ((F.metric p.1).inner p.2 ((F.connection p.1).connection V p.2 (U p.2)) (c i) *
        B (Function.update (fun i => X i p.2) r (c j))) at h
  simp only [← hB, hc, OrthonormalBasis.coe_toBasis] at h
  convert h using 1
  rfl

lemma contMDiffAt_covariantTensorDerivative_fields
    (F : RicciFlow n M J) {k : ℕ} {T : ℝ → CovariantTensorEvaluation n M k}
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ X : Fin k → (y : M) → TangentSpace (𝓡 n) y,
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) x) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, x))
    {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).covariantTensorDerivative (T p.1) p.2
        (fun i => X i p.2)) (t, x) := by
  let Y := fun i : Fin k => X i.succ
  have hY (i : Fin k) := hX i.succ
  have hraw := Poincare.Manifold.contMDiffAt_mvfderiv_spatial (hreg Y hY) (hX 0)
  have hslot (i) := F.contMDiffAt_tensor_update_connection_fields ht hT hreg hY (hX 0) (hY i) i
  have h := hraw.sub (ContMDiffAt.sum (t := Finset.univ) fun i _ => hslot i)
  apply h.congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i : Fin k, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (Y i)) y :=
    Filter.eventually_all.mpr fun i =>
      LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt (hY i)
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually hnear] with p hp
  have hfield := (F.connection p.1).covariantTensorDerivative_on_fields
    (hT p.1) Y p.2 hp (X 0 p.2)
  have heq : Fin.cons (X 0 p.2) (fun i : Fin k => Y i p.2) = fun i => X i p.2 := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simpa only [heq, Pi.sub_apply] using hfield

lemma contMDiffAt_tensorTrace_fields
    (F : RicciFlow n M J) {k : ℕ} {T : ℝ → CovariantTensorEvaluation n M (k + 2)}
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ X : Fin (k + 2) → (y : M) → TangentSpace (𝓡 n) y,
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) x) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, x))
    {X : Fin k → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.metric p.1).tensorTrace (T p.1) p.2
        (fun i => X i p.2)) (t, x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let b := (F.metric t).orthonormalBasis x
  let e := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G : ℝ × M → Matrix _ _ ℝ := fun p i j =>
    (F.metric p.1).inner p.2 (e i p.2) (e j p.2)
  have he (i) : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (e i)) x := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) _ (b i)
  have hG (i j) := F.contMDiffAt_inner_fields ht (he i) (he j)
  have hGx : G (t, x) = 1 := by
    ext i j
    change (F.metric t).inner x (e i x) (e j x) = _
    simp only [e, FiberBundle.extend_apply_self]
    exact b.inner_eq_ite i j
  have hi := Poincare.Manifold.contMDiffAt_matrix_inv_entry G (t, x) hG (by simp [hGx])
  have hA (i j) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => T p.1 p.2
        (Fin.cons (e i p.2) (Fin.cons (e j p.2) (fun r => X r p.2)))) (t, x) := by
    have h := hreg (Fin.cons (e i) (Fin.cons (e j) X))
      (Fin.cases (he i) (Fin.cases (he j) hX))
    convert h using 1
    funext p
    congr 1
    ext r
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) r
  have hsum := ContMDiffAt.sum (t := Finset.univ) fun i _ =>
    ContMDiffAt.sum (t := Finset.univ) fun j _ => (hi i j).mul (hA i j)
  apply hsum.congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually (eventually_exists_basis_extend x b.toBasis)] with p hp
  obtain ⟨c, hc⟩ := hp
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric p.1).toRiemannianMetric⟩
  obtain ⟨B, hB⟩ := (hT p.1).1 p.2
  have h := bilinear_sum_basis_eq_inverse_gram (bilinearOfTensorCons B (fun i => X i p.2))
    c ((F.metric p.1).orthonormalBasis p.2)
  change (∑ i, B (Fin.cons ((F.metric p.1).orthonormalBasis p.2 i)
    (Fin.cons ((F.metric p.1).orthonormalBasis p.2 i) (fun r => X r p.2)))) =
    ∑ i, ∑ j, (Matrix.of (fun i j => (F.metric p.1).inner p.2 (c i) (c j)))⁻¹ i j *
      B (Fin.cons (c i) (Fin.cons (c j) (fun r => X r p.2))) at h
  simp only [← hB, hc, OrthonormalBasis.coe_toBasis] at h
  exact h

end PoincareConjecture.RicciFlow
