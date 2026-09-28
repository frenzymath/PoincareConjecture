import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Directions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Spacetime.M
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedSpatialContact






set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture Poincare.VectorBundle

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



lemma continuousAt_tensor_family_evaluation
    {A : Type*} [TopologicalSpace A] {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M k} (hT : ∀ s, IsSmoothCovariantTensor (T s))
    {t : A → ℝ} {x : A → M} {q : A}
    (hreg : ∀ O : Set M, IsOpen O → x q ∈ O →
      ∀ X : Fin k → (y : M) → TangentSpace (𝓡 n) y,
      (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (X i)) O) →
      ContinuousAt (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t q, x q))
    (ht : ContinuousAt t q) (hx : ContinuousAt x q)
    {X : (a : A) → Fin k → TangentSpace (𝓡 n) (x a)}
    (hX : ∀ i, ContinuousAt (fun a =>
      (⟨x a, X a i⟩ : TotalSpace (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)))) q) :
    ContinuousAt (fun a => T (t a) (x a) (X a)) q := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V (x q)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let S := e.localFrame b
  let C (a : A) (i : Fin k) (j : Fin n) := b.repr (e ⟨x a, X a i⟩).2 j
  have hxq : x q ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V (x q)
  have hC (i : Fin k) (j : Fin n) : ContinuousAt (fun a => C a i j) q := by
    have he : ContinuousAt e (⟨x q, X q i⟩ : TotalSpace E V) :=
      e.continuousAt (show (⟨x q, X q i⟩ : TotalSpace E V) ∈ e.source from hxq)
    have heX : ContinuousAt (fun a : A => e ⟨x a, X a i⟩) q :=
      he.comp (f := fun a : A => (⟨x a, X a i⟩ : TotalSpace E V)) (hX i)
    exact ((b.coord j).toContinuousLinearMap.continuous.continuousAt.comp heX.snd)
  have hS (a : Fin k → Fin n) : ContinuousAt
      (fun p : ℝ × M => T p.1 p.2 (fun i => S (a i) p.2)) (t q, x q) :=
    hreg e.baseSet e.open_baseSet hxq _ (fun i => e.contMDiffOn_localFrame_baseSet ∞ b (a i))
  have hsum : ContinuousAt (fun z => ∑ a : Fin k → Fin n,
      (∏ i, C z i (a i)) * T (t z) (x z) (fun i => S (a i) (x z))) q :=
    tendsto_finsetSum _ fun a _ =>
      (tendsto_finsetProd _ fun i _ => hC i (a i)).mul
        ((hS a).comp (f := fun z : A => (t z, x z)) (ht.prodMk hx))
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hx.eventually (e.open_baseSet.mem_nhds hxq)] with a ha
  obtain ⟨L, hL⟩ := (hT (t a)).1 (x a)
  simp_rw [hL]
  have hdecomp : X a = fun i => ∑ j : Fin n, C a i j • S j (x a) := by
    funext i
    have h := (e.basisAt b ha).sum_repr (X a i)
    simpa only [S, C, e.localFrame_apply_of_mem_baseSet b ha,
      Bundle.Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, Bundle.Trivialization.linearEquivAt_apply] using h.symm
  rw [hdecomp, L.map_sum]
  simp only [L.map_smul_univ, smul_eq_mul]

private lemma eventually_basis_extend {ι : Type} (x : M)
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    ∀ᶠ y in 𝓝 x, ∃ c : Module.Basis ι ℝ (TangentSpace (𝓡 n) y),
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

private lemma contMDiffAt_inner_two_connections {J : Set ℝ}
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X Y Z W : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.metric p.1).inner p.2
        ((F.connection p.1).connection Y p.2 (X p.2))
        ((F.connection p.1).connection W p.2 (Z p.2))) (t, x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let b := (F.metric t).orthonormalBasis x
  let e := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let G : ℝ × M → Matrix _ _ ℝ := fun p i j =>
    (F.metric p.1).inner p.2 (e i p.2) (e j p.2)
  have he (i) : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (e i)) x :=
    FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) _ (b i)
  have hG (i j) := F.contMDiffAt_inner_fields ht (he i) (he j)
  have hGx : G (t, x) = 1 := by
    ext i j
    change (F.metric t).inner x (e i x) (e j x) = _
    simp only [e, FiberBundle.extend_apply_self]
    exact b.inner_eq_ite i j
  have hi := Poincare.Manifold.contMDiffAt_matrix_inv_entry G (t, x) hG (by simp [hGx])
  have hA (i) := F.contMDiffAt_inner_connection_fields ht hX hY (he i)
  have hB (j) := F.contMDiffAt_inner_connection_fields ht hZ hW (he j)
  have hsum := ContMDiffAt.sum (t := Finset.univ) fun i _ =>
    ContMDiffAt.sum (t := Finset.univ) fun j _ => (hi i j).mul ((hA i).mul (hB j))
  apply hsum.congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually (eventually_basis_extend x b.toBasis)] with p hp
  obtain ⟨c, hc⟩ := hp
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric p.1).toRiemannianMetric⟩
  have h := linear_apply_eq_inverse_gram
    (((F.metric p.1).inner p.2 ((F.connection p.1).connection W p.2 (Z p.2))).toLinearMap)
    ((F.connection p.1).connection Y p.2 (X p.2)) c ((F.metric p.1).orthonormalBasis p.2)
  change (F.metric p.1).inner p.2 ((F.connection p.1).connection W p.2 (Z p.2))
    ((F.connection p.1).connection Y p.2 (X p.2)) =
    ∑ i, ∑ j, (Matrix.of (fun i j => (F.metric p.1).inner p.2 (c i) (c j)))⁻¹ i j *
      ((F.metric p.1).inner p.2 ((F.connection p.1).connection Y p.2 (X p.2)) (c i) *
        (F.metric p.1).inner p.2 ((F.connection p.1).connection W p.2 (Z p.2)) (c j)) at h
  rw [(F.metric p.1).symm] at h
  simp only [hc, OrthonormalBasis.coe_toBasis] at h
  convert h using 1
  rfl



lemma contMDiffAt_curvatureTensor_fields_on {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M} {O : Set M} (hO : IsOpen O) (hx : x ∈ O)
    {X : Fin 4 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (X i)) O) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).curvatureTensor p.2
        (X 0 p.2) (X 1 p.2) (X 2 p.2) (X 3 p.2)) (t, x) := by
  have hXa i := (hX i).contMDiffAt (hO.mem_nhds hx)
  have hA := Poincare.Manifold.contMDiffAt_mvfderiv_spatial
    (F.contMDiffAt_inner_connection_fields ht (hXa 1) (hXa 3) (hXa 2)) (hXa 0)
  have hB := contMDiffAt_inner_two_connections F ht (hXa 1) (hXa 3) (hXa 0) (hXa 2)
  have hC' := Poincare.Manifold.contMDiffAt_mvfderiv_spatial
    (F.contMDiffAt_inner_connection_fields ht (hXa 0) (hXa 3) (hXa 2)) (hXa 1)
  have hD := contMDiffAt_inner_two_connections F ht (hXa 0) (hXa 3) (hXa 1) (hXa 2)
  have hE := F.contMDiffAt_inner_connection_fields ht
    (LeviCivitaData.contMDiffAt_mlieBracket (hXa 0) (hXa 1)) (hXa 3) (hXa 2)
  apply (((hA.sub hB).sub (hC'.sub hD)).sub hE).congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards [hsnd.eventually (hO.mem_nhds hx)] with p hp
  have hXp i := (hX i).contMDiffAt (hO.mem_nhds hp)
  let D := F.connection p.1
  have hcompat₁ := D.horizon_mvfderiv_inner (X 0)
    ((D.contMDiffAt_covariantDerivativeOnFields (hXp 1) (hXp 3)).mdifferentiableAt (by simp))
    ((hXp 2).mdifferentiableAt (by simp))
  have hcompat₂ := D.horizon_mvfderiv_inner (X 1)
    ((D.contMDiffAt_covariantDerivativeOnFields (hXp 0) (hXp 3)).mdifferentiableAt (by simp))
    ((hXp 2).mdifferentiableAt (by simp))
  have heq := (hC.tensor_calculus n M (F.metric p.1) D).2.2.2.2
    O hO (X 0) (X 1) (X 3) (hX 0) (hX 1) (hX 3) p.2 hp
  unfold LeviCivitaData.curvatureTensor
  rw [← heq]
  simp only [LeviCivitaData.curvatureOnFields, map_sub, _root_.sub_apply]
  unfold LeviCivitaData.covariantDerivativeOnFields at hcompat₁ hcompat₂
  dsimp only [Pi.sub_apply, D] at hcompat₁ hcompat₂ ⊢
  linarith only [hcompat₁, hcompat₂]



abbrev HamiltonDirection (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :=
  fiberFamilies (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n) (M := M)) (Fin n) ×
    EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n)



noncomputable def hamiltonDirectionQuadratic {J : Set ℝ} (F : RicciFlow n M J)
    (T₀ : ℝ) (t : ℝ) (q : HamiltonDirection n M) : ℝ :=
  let x := q.1.val.1
  let e := FiberFamily.vector q.1
  let U := fun a b => q.2 (Sum.inl (a, b))
  let W := fun a => q.2 (Sum.inr a)
  (∑ a, ∑ b, hamiltonM (F.connection t) (t - T₀) x (e a) (e b) * W a * W b) +
    2 * (∑ a, ∑ b, ∑ c, hamiltonP (F.connection t) x (e a) (e b) (e c) * U a b * W c) +
    (∑ a, ∑ b, ∑ c, ∑ d,
      (F.connection t).curvatureTensor x (e a) (e b) (e c) (e d) * U a b * U c d)

private lemma continuousAt_tensor_direction_fields {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M k} (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (t : ℝ) (q : HamiltonDirection n M)
    (hreg : ∀ O : Set M, IsOpen O → q.1.val.1 ∈ O →
      ∀ X : Fin k → (y : M) → TangentSpace (𝓡 n) y,
      (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (X i)) O) →
      ContinuousAt (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, q.1.val.1))
    (a : Fin k → Fin n) :
    ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      T p.1 p.2.1.val.1 (fun i => FiberFamily.vector p.2.1 (a i))) (t, q) := by
  apply continuousAt_tensor_family_evaluation hT hreg continuousAt_fst
    ((continuous_fst.comp continuous_subtype_val).continuousAt.comp
      (f := fun p : ℝ × HamiltonDirection n M => p.2.1) continuousAt_snd.fst)
  intro i
  exact (FiberFamily.continuous_vector (F := EuclideanSpace ℝ (Fin n))
    (E := TangentSpace (𝓡 n)) (a i)).continuousAt.comp
      (f := fun p : ℝ × HamiltonDirection n M => p.2.1) continuousAt_snd.fst



theorem continuousAt_hamiltonDirectionQuadratic {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (T₀ : ℝ)
    {t : ℝ} (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (q : HamiltonDirection n M) :
    ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      hamiltonDirectionQuadratic F T₀ p.1 p.2) (t, q) := by
  have hD s := hC.tensor_calculus n M (F.metric s) (F.connection s)
  have hM (a b : Fin n) : ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      hamiltonM (F.connection p.1) (p.1 - T₀) p.2.1.val.1
        (FiberFamily.vector p.2.1 a) (FiberFamily.vector p.2.1 b)) (t, q) := by
    exact continuousAt_tensor_direction_fields
      (fun s => hamiltonM_isSmoothCovariantTensor (F.connection s) (hD s) (s - T₀)) t q
      (fun O hO hx X hX => (contMDiffAt_hamiltonM_fields hC F T₀ ht hτ
        (fun i => (hX i).contMDiffAt (hO.mem_nhds hx))).continuousAt) ![a, b]
  have hP (a b c : Fin n) : ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      hamiltonP (F.connection p.1) p.2.1.val.1
        (FiberFamily.vector p.2.1 a) (FiberFamily.vector p.2.1 b)
        (FiberFamily.vector p.2.1 c)) (t, q) := by
    exact continuousAt_tensor_direction_fields
      (fun s => hamiltonP_isSmoothCovariantTensor (F.connection s) (hD s)) t q
      (fun O hO hx X hX => (contMDiffAt_hamiltonP_fields hC F ht
        (fun i => (hX i).contMDiffAt (hO.mem_nhds hx))).continuousAt) ![a, b, c]
  have hR (a b c d : Fin n) : ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      (F.connection p.1).curvatureTensor p.2.1.val.1
        (FiberFamily.vector p.2.1 a) (FiberFamily.vector p.2.1 b)
        (FiberFamily.vector p.2.1 c) (FiberFamily.vector p.2.1 d)) (t, q) := by
    exact continuousAt_tensor_direction_fields (fun s => (hD s).1) t q
      (fun O hO hx X hX => (contMDiffAt_curvatureTensor_fields_on hC F ht hO hx hX).continuousAt)
      ![a, b, c, d]
  have hc (i : (Fin n × Fin n) ⊕ Fin n) : ContinuousAt
      (fun p : ℝ × HamiltonDirection n M => p.2.2 i) (t, q) :=
    ((PiLp.continuous_apply 2 _ i).comp (continuous_snd.comp continuous_snd)).continuousAt
  have hsumM := tendsto_finsetSum Finset.univ fun a _ =>
    tendsto_finsetSum Finset.univ fun b _ => ((hM a b).mul (hc (Sum.inr a))).mul (hc (Sum.inr b))
  have hsumP := tendsto_finsetSum Finset.univ fun a _ =>
    tendsto_finsetSum Finset.univ fun b _ => tendsto_finsetSum Finset.univ fun c _ =>
      ((hP a b c).mul (hc (Sum.inl (a, b)))).mul (hc (Sum.inr c))
  have hsumR := tendsto_finsetSum Finset.univ fun a _ =>
    tendsto_finsetSum Finset.univ fun b _ => tendsto_finsetSum Finset.univ fun c _ =>
      tendsto_finsetSum Finset.univ fun d _ =>
        ((hR a b c d).mul (hc (Sum.inl (a, b)))).mul (hc (Sum.inl (c, d)))
  exact (hsumM.add (continuousAt_const.mul hsumP)).add hsumR



theorem continuousOn_hamiltonDirectionQuadratic {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (T₀ : ℝ)
    {a b : ℝ} (hJ : Icc a b ⊆ interior J) (hτ : ∀ t ∈ Icc a b, t - T₀ ≠ 0) :
    ContinuousOn (fun p : ℝ × HamiltonDirection n M =>
      hamiltonDirectionQuadratic F T₀ p.1 p.2) (Icc a b ×ˢ univ) := by
  rintro ⟨t, q⟩ ht
  exact (continuousAt_hamiltonDirectionQuadratic hC F T₀ (hJ ht.1) (hτ t ht.1) q).continuousWithinAt



noncomputable def perturbedHamiltonDirectionQuadratic {J : Set ℝ} (F : RicciFlow n M J)
    (T₀ : ℝ) (φ : ℝ × M → ℝ) (ψ : ℝ → ℝ) (t : ℝ) (q : HamiltonDirection n M) : ℝ :=
  let x := q.1.val.1
  let e := FiberFamily.vector q.1
  let U := fun a b => q.2 (Sum.inl (a, b))
  let W := fun a => q.2 (Sum.inr a)
  hamiltonDirectionQuadratic F T₀ t q +
    φ (t, x) * (∑ a, ∑ b, (F.metric t).inner x (e a) (e b) * W a * W b) +
    ψ t * (∑ a, ∑ b, ∑ c, ∑ d,
      metricTwoFormIdentity (F.metric t) x ![e a, e b, e c, e d] * U a b * U c d)



theorem continuousAt_perturbedHamiltonDirectionQuadratic {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (T₀ : ℝ)
    {φ : ℝ × M → ℝ} {ψ : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ interior J) (hτ : t - T₀ ≠ 0) (q : HamiltonDirection n M)
    (hφ : ContinuousAt φ (t, q.1.val.1)) (hψ : ContinuousAt ψ t) :
    ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      perturbedHamiltonDirectionQuadratic F T₀ φ ψ p.1 p.2) (t, q) := by
  have hg (a b : Fin n) : ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      (F.metric p.1).inner p.2.1.val.1
        (FiberFamily.vector p.2.1 a) (FiberFamily.vector p.2.1 b)) (t, q) := by
    exact continuousAt_tensor_direction_fields
      (fun s => metric_isSmoothCovariantTensor (F.metric s)) t q
      (fun O hO hx X hX => (F.contMDiffAt_inner_fields ht
        ((hX 0).contMDiffAt (hO.mem_nhds hx)) ((hX 1).contMDiffAt (hO.mem_nhds hx))).continuousAt)
      ![a, b]
  have hI (a b c d : Fin n) : ContinuousAt (fun p : ℝ × HamiltonDirection n M =>
      metricTwoFormIdentity (F.metric p.1) p.2.1.val.1
        ![FiberFamily.vector p.2.1 a, FiberFamily.vector p.2.1 b,
          FiberFamily.vector p.2.1 c, FiberFamily.vector p.2.1 d]) (t, q) :=
    (((hg a c).mul (hg b d)).sub ((hg a d).mul (hg b c))).div_const 2
  have hc (i : (Fin n × Fin n) ⊕ Fin n) : ContinuousAt
      (fun p : ℝ × HamiltonDirection n M => p.2.2 i) (t, q) :=
    ((PiLp.continuous_apply 2 _ i).comp (continuous_snd.comp continuous_snd)).continuousAt
  have hsumg := tendsto_finsetSum Finset.univ fun a _ =>
    tendsto_finsetSum Finset.univ fun b _ => ((hg a b).mul (hc (Sum.inr a))).mul (hc (Sum.inr b))
  have hsumI := tendsto_finsetSum Finset.univ fun a _ =>
    tendsto_finsetSum Finset.univ fun b _ => tendsto_finsetSum Finset.univ fun c _ =>
      tendsto_finsetSum Finset.univ fun d _ =>
        ((hI a b c d).mul (hc (Sum.inl (a, b)))).mul (hc (Sum.inl (c, d)))
  have hx : ContinuousAt (fun p : ℝ × HamiltonDirection n M => p.2.1.val.1) (t, q) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.comp
      (f := fun p : ℝ × HamiltonDirection n M => p.2.1) continuousAt_snd.fst
  have hφ' : ContinuousAt (fun p : ℝ × HamiltonDirection n M => φ (p.1, p.2.1.val.1))
      (t, q) := hφ.comp (f := fun p : ℝ × HamiltonDirection n M => (p.1, p.2.1.val.1))
        (continuousAt_fst.prodMk hx)
  exact ((continuousAt_hamiltonDirectionQuadratic hC F T₀ ht hτ q).add
    (hφ'.mul hsumg)).add ((hψ.comp continuousAt_fst).mul hsumI)



theorem continuousOn_perturbedHamiltonDirectionQuadratic {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (T₀ : ℝ)
    {φ : ℝ × M → ℝ} {ψ : ℝ → ℝ} {a b : ℝ}
    (hJ : Icc a b ⊆ interior J) (hτ : ∀ t ∈ Icc a b, t - T₀ ≠ 0)
    (hφ : ContinuousOn φ (interior J ×ˢ univ)) (hψ : ContinuousOn ψ (interior J)) :
    ContinuousOn (fun p : ℝ × HamiltonDirection n M =>
      perturbedHamiltonDirectionQuadratic F T₀ φ ψ p.1 p.2) (Icc a b ×ˢ univ) := by
  rintro ⟨t, q⟩ ht
  have ht' := hJ ht.1
  exact (continuousAt_perturbedHamiltonDirectionQuadratic hC F T₀ ht' (hτ t ht.1) q
    (hφ.continuousAt ((isOpen_interior.prod isOpen_univ).mem_nhds ⟨ht', mem_univ _⟩))
    (hψ.continuousAt (isOpen_interior.mem_nhds ht'))).continuousWithinAt

end Poincare.RicciFlow.Harnack
