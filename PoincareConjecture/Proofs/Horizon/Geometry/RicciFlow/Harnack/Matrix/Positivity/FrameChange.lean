import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.BasisChange
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.PerturbedTimeContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.DirectionEvaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped BigOperators Manifold ContDiff Bundle

namespace Poincare.RicciFlow.Harnack

section Coordinates

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def hamiltonVectorCoordinates (C : J → I → ℝ) (W : J → ℝ) : I → ℝ :=
  fun a => ∑ i, C i a * W i

noncomputable def hamiltonTwoFormCoordinates (C : J → I → ℝ)
    (U : J → J → ℝ) : I → I → ℝ :=
  fun a b => ∑ i, ∑ j, C i a * C j b * U i j

omit [Fintype I] in
lemma hamiltonTwoFormCoordinates_skew (C : J → I → ℝ) (U : J → J → ℝ)
    (hU : ∀ i j, U i j = -U j i) :
    ∀ a b, hamiltonTwoFormCoordinates C U a b = -hamiltonTwoFormCoordinates C U b a := by
  intro a b
  simp only [hamiltonTwoFormCoordinates, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hU i j]
  ring

private lemma sum_coordinate_pairing {K L : Type*} [Fintype K] [Fintype L]
    (C : J → I → ℝ) (D : L → K → ℝ) (B : I → K → ℝ)
    (W : J → ℝ) (V : L → ℝ) :
    (∑ i, ∑ j, (∑ a, ∑ b, C i a * B a b * D j b) * W i * V j) =
      ∑ a, ∑ b, B a b * hamiltonVectorCoordinates C W a *
        hamiltonVectorCoordinates D V b := by
  simp only [hamiltonVectorCoordinates, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ a, ∑ b, ∑ j, C i a * B a b * D j b * W i * V j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm_cycle.symm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, C i a * B a b * D j b * W i * V j :=
      Finset.sum_comm_cycle.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Coordinates

open PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : Type*} [Fintype I]

noncomputable def hamiltonFrameCoordinates (g : RiemannianMetric n M) (x : M)
    (e : I → TangentSpace (𝓡 n) x) :
    I → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ :=
  fun i a => g.inner x (e i) (g.orthonormalBasis x a)

lemma hamiltonVectorCoordinates_eq_zero_iff (g : RiemannianMetric n M)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (he : LinearIndependent ℝ e) (W : I → ℝ) :
    hamiltonVectorCoordinates (hamiltonFrameCoordinates g x e) W = 0 ↔ W = 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  · intro hW
    have hdecomp (i : I) : e i = ∑ a,
        hamiltonFrameCoordinates g x e i a • g.orthonormalBasis x a := by
      have h := ((g.orthonormalBasis x).sum_repr' (e i)).symm
      change e i = ∑ a, g.inner x (g.orthonormalBasis x a) (e i) •
        g.orthonormalBasis x a at h
      simpa only [hamiltonFrameCoordinates, g.symm] using h
    have hsum : ∑ i, W i • e i = 0 := by
      simp_rw [hdecomp, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, mul_comm (W _)]
      change (∑ a, hamiltonVectorCoordinates (hamiltonFrameCoordinates g x e) W a •
        g.orthonormalBasis x a) = 0
      rw [hW]
      simp
    exact funext ((Fintype.linearIndependent_iff.mp he) W hsum)
  · rintro rfl
    funext a
    simp [hamiltonVectorCoordinates]

lemma hamiltonTwoFormCoordinates_eq_zero_iff (g : RiemannianMetric n M)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (he : LinearIndependent ℝ e)
    (U : I → I → ℝ) :
    hamiltonTwoFormCoordinates (hamiltonFrameCoordinates g x e) U = 0 ↔ U = 0 := by
  classical
  let C := hamiltonFrameCoordinates g x e
  constructor
  · intro hU
    have hrow (a) : (fun j => ∑ i, C i a * U i j) = 0 := by
      apply (hamiltonVectorCoordinates_eq_zero_iff g x e he _).mp
      funext b
      have hab := congrFun (congrFun hU a) b
      change (∑ j, C j b * ∑ i, C i a * U i j) = 0
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simpa only [hamiltonTwoFormCoordinates, Pi.zero_apply, mul_left_comm, mul_assoc, C]
        using hab
    have hcol (j) : (fun i => U i j) = 0 := by
      apply (hamiltonVectorCoordinates_eq_zero_iff g x e he _).mp
      funext a
      exact congrFun (hrow a) j
    funext i j
    exact congrFun (hcol j) i
  · rintro rfl
    funext a b
    simp [hamiltonTwoFormCoordinates]

private lemma sqrt_sum_sq_eq_zero_iff (f : I → ℝ) :
    Real.sqrt (∑ i, f i ^ 2) = 0 ↔ f = 0 := by
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg (f i))]
  constructor
  · intro h
    funext i
    exact sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).mp h i (Finset.mem_univ i))
  · rintro rfl
    simp

lemma hamiltonCoordinates_sqrt_nonzero (g : RiemannianMetric n M)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (he : LinearIndependent ℝ e)
    (U : I → I → ℝ) (W : I → ℝ) (hnonzero : U ≠ 0 ∨ W ≠ 0) :
    let C := hamiltonFrameCoordinates g x e
    Real.sqrt (∑ a, ∑ b, hamiltonTwoFormCoordinates C U a b ^ 2) ≠ 0 ∨
      Real.sqrt (∑ a, hamiltonVectorCoordinates C W a ^ 2) ≠ 0 := by
  dsimp only
  rcases hnonzero with hU | hW
  · left
    intro hz
    have hpair := (sqrt_sum_sq_eq_zero_iff
      (fun ab : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        hamiltonTwoFormCoordinates (hamiltonFrameCoordinates g x e) U ab.1 ab.2)).mp
        (by simpa only [Fintype.sum_prod_type] using hz)
    apply hU
    apply (hamiltonTwoFormCoordinates_eq_zero_iff g x e he U).mp
    funext a b
    exact congrFun hpair (a, b)
  · right
    intro hz
    exact hW ((hamiltonVectorCoordinates_eq_zero_iff g x e he W).mp
      ((sqrt_sum_sq_eq_zero_iff _).mp hz))

theorem hamiltonFrameCoordinates_sqrt_nonzero (g : RiemannianMetric n M)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (he : LinearIndependent ℝ e)
    (z : EuclideanSpace ℝ ((I × I) ⊕ I)) (hz : ‖z‖ = 1) :
    let C := hamiltonFrameCoordinates g x e
    let U := fun i j => z (Sum.inl (i, j))
    let W := fun i => z (Sum.inr i)
    Real.sqrt (∑ a, ∑ b, hamiltonTwoFormCoordinates C U a b ^ 2) ≠ 0 ∨
      Real.sqrt (∑ a, hamiltonVectorCoordinates C W a ^ 2) ≠ 0 := by
  apply hamiltonCoordinates_sqrt_nonzero g x e he
  by_contra h
  push Not at h
  have hz0 : z = 0 := by
    ext (ij | i)
    · exact congrFun (congrFun h.1 ij.1) ij.2
    · exact congrFun h.2 i
  simp only [hz0, norm_zero, zero_ne_one] at hz

omit [Fintype I] in

theorem hamiltonDirectionCoordinates_sqrt_nonzero (g : RiemannianMetric n M)
    (q : HamiltonDirection n M)
    (he : LinearIndependent ℝ (Poincare.VectorBundle.FiberFamily.vector q.1))
    (hq : ‖q.2‖ = 1) :
    let C := hamiltonFrameCoordinates g q.1.val.1
      (Poincare.VectorBundle.FiberFamily.vector q.1)
    let U := fun i j => q.2 (Sum.inl (i, j))
    let W := fun i => q.2 (Sum.inr i)
    Real.sqrt (∑ a, ∑ b, hamiltonTwoFormCoordinates C U a b ^ 2) ≠ 0 ∨
      Real.sqrt (∑ a, hamiltonVectorCoordinates C W a ^ 2) ≠ 0 :=
  hamiltonFrameCoordinates_sqrt_nonzero g q.1.val.1 _ he q.2 hq

lemma tensor_two_contraction_coordinates (g : RiemannianMetric n M)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (W V : I → ℝ) :
    let C := hamiltonFrameCoordinates g x e
    let b := g.orthonormalBasis x
    (∑ i, ∑ j, T x ![e i, e j] * W i * V j) =
      ∑ a, ∑ c, T x ![b a, b c] * hamiltonVectorCoordinates C W a *
        hamiltonVectorCoordinates C V c := by
  dsimp only
  simpa only [hamiltonFrameCoordinates, ← tensor_two_expansion g hT] using
    sum_coordinate_pairing (hamiltonFrameCoordinates g x e) (hamiltonFrameCoordinates g x e)
      (fun a c => T x ![g.orthonormalBasis x a, g.orthonormalBasis x c]) W V

lemma tensor_three_contraction_coordinates (g : RiemannianMetric n M)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (U : I → I → ℝ) (W : I → ℝ) :
    let C := hamiltonFrameCoordinates g x e
    let b := g.orthonormalBasis x
    (∑ i, ∑ j, ∑ k, T x ![e i, e j, e k] * U i j * W k) =
      ∑ a, ∑ c, ∑ d, T x ![b a, b c, b d] * hamiltonTwoFormCoordinates C U a c *
        hamiltonVectorCoordinates C W d := by
  let C := hamiltonFrameCoordinates g x e
  have h := sum_coordinate_pairing
    (fun (ij : I × I) (ac : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) => C ij.1 ac.1 * C ij.2 ac.2) C
    (fun ac d => T x ![g.orthonormalBasis x ac.1, g.orthonormalBasis x ac.2,
      g.orthonormalBasis x d]) (fun ij => U ij.1 ij.2) W
  simp only [Fintype.sum_prod_type] at h
  simpa only [C, hamiltonVectorCoordinates, hamiltonTwoFormCoordinates,
    hamiltonFrameCoordinates, Fintype.sum_prod_type, ← tensor_three_expansion g hT] using h

lemma tensor_four_contraction_coordinates (g : RiemannianMetric n M)
    {T : CovariantTensorEvaluation n M 4} (hT : IsSmoothCovariantTensor T)
    (x : M) (e : I → TangentSpace (𝓡 n) x) (U V : I → I → ℝ) :
    let C := hamiltonFrameCoordinates g x e
    let b := g.orthonormalBasis x
    (∑ i, ∑ j, ∑ k, ∑ l, T x ![e i, e j, e k, e l] * U i j * V k l) =
      ∑ a, ∑ c, ∑ d, ∑ f, T x ![b a, b c, b d, b f] *
        hamiltonTwoFormCoordinates C U a c * hamiltonTwoFormCoordinates C V d f := by
  let C := hamiltonFrameCoordinates g x e
  let D := fun (ij : I × I) (ac : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
    Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) => C ij.1 ac.1 * C ij.2 ac.2
  have h := sum_coordinate_pairing D D
    (fun ac df => T x ![g.orthonormalBasis x ac.1, g.orthonormalBasis x ac.2,
      g.orthonormalBasis x df.1, g.orthonormalBasis x df.2])
    (fun ij => U ij.1 ij.2) (fun kl => V kl.1 kl.2)
  simp only [Fintype.sum_prod_type, D, mul_assoc] at h
  have hexp (i j k l) := tensor_four_expansion g hT x (e i) (e j) (e k) (e l)
  simp only [mul_assoc] at hexp
  simpa only [C, hamiltonVectorCoordinates, hamiltonTwoFormCoordinates,
    hamiltonFrameCoordinates, Fintype.sum_prod_type, mul_assoc, ← hexp] using h

omit [Fintype I] in

theorem perturbedHamiltonDirectionQuadratic_eq_fixed {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (T₀ t : ℝ)
    (φ : ℝ × M → ℝ) (ψ : ℝ → ℝ) (q : HamiltonDirection n M) (s : ℝ) :
    let C := hamiltonFrameCoordinates (F.metric t) q.1.val.1
      (Poincare.VectorBundle.FiberFamily.vector q.1)
    let U := fun i j => q.2 (Sum.inl (i, j))
    let W := fun i => q.2 (Sum.inr i)
    perturbedHamiltonDirectionQuadratic F T₀ φ ψ s q =
      perturbedHamiltonFixedQuadratic F T₀ t q.1.val.1 (fun r y => φ (r, y)) ψ
        (hamiltonTwoFormCoordinates C U) (hamiltonVectorCoordinates C W) s := by
  let x := q.1.val.1
  let e := Poincare.VectorBundle.FiberFamily.vector q.1
  let U := fun i j => q.2 (Sum.inl (i, j))
  let W := fun i => q.2 (Sum.inr i)
  let D := F.connection s
  have hD := hC.tensor_calculus n M (F.metric s) D
  have hM := tensor_two_contraction_coordinates (F.metric t)
    (hamiltonM_isSmoothCovariantTensor D hD (s - T₀)) x e W W
  have hP := tensor_three_contraction_coordinates (F.metric t)
    (hamiltonP_isSmoothCovariantTensor D hD) x e U W
  have hR := tensor_four_contraction_coordinates (F.metric t) hD.1 x e U U
  have hg := tensor_two_contraction_coordinates (F.metric t)
    (metric_isSmoothCovariantTensor (F.metric s)) x e W W
  have hI := tensor_four_contraction_coordinates (F.metric t)
    (metricTwoFormIdentity_isSmooth (F.metric s)) x e U U
  dsimp only at hM hP hR hg hI
  simp only [LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hM hP hR hg
  change (_ + φ (s, x) * _ + ψ s * _) = _
  dsimp only [perturbedHamiltonDirectionQuadratic, hamiltonDirectionQuadratic]
  change ((∑ i, ∑ j, hamiltonM D (s - T₀) x (e i) (e j) * W i * W j) +
    2 * (∑ i, ∑ j, ∑ k, hamiltonP D x (e i) (e j) (e k) * U i j * W k) +
    (∑ i, ∑ j, ∑ k, ∑ l, D.curvatureTensor x (e i) (e j) (e k) (e l) * U i j * U k l) +
    φ (s, x) * (∑ i, ∑ j, (F.metric s).inner x (e i) (e j) * W i * W j) +
    ψ s * (∑ i, ∑ j, ∑ k, ∑ l,
      metricTwoFormIdentity (F.metric s) x ![e i, e j, e k, e l] * U i j * U k l)) = _
  rw [hM, hP, hR, hg, hI]
  simp only [perturbedHamiltonFixedQuadratic, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  dsimp only [x, D, U, W, e]
  ring

end Poincare.RicciFlow.Harnack
