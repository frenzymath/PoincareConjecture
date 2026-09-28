import PoincareConjecture.Proofs.M04.CurvatureEnergyTime
import PoincareConjecture.Proofs.M04.CurvatureEnergyBochner
import PoincareConjecture.Proofs.M04.TensorNormBounds
import PoincareConjecture.Proofs.M35.RawFlow.Completeness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def lichnerowiczReaction (D : LeviCivitaData g)
    (H : CovariantTensorEvaluation n M 2) : CovariantTensorEvaluation n M 2 :=
  fun x v =>
    2 * (∑ p, ∑ q, D.curvatureTensor x (v 0) (g.orthonormalBasis x p)
      (v 1) (g.orthonormalBasis x q) * H x ![g.orthonormalBasis x p,
        g.orthonormalBasis x q]) -
    ∑ j, ∑ q, D.ricci x (v j) (g.orthonormalBasis x q) *
      H x (Function.update v j (g.orthonormalBasis x q))



theorem hasDerivAt_lichnerowicz_normSq {J : Set ℝ} (F : RicciFlow n M J)
    (H : ℝ → CovariantTensorEvaluation n M 2)
    (hH : ∀ s, IsSmoothCovariantTensor (H s)) {t : ℝ} (ht : t ∈ interior J)
    (x : M)
    (hheat : ∀ v, HasDerivAt (fun s => H s x v)
      ((F.connection t).tensorLaplacian (H t) x v +
        lichnerowiczReaction (F.connection t) (H t) x v) t) :
    let g := F.metric t
    let D := F.connection t
    let b := g.orthonormalBasis x
    HasDerivAt (fun s => ((F.metric s).tensorNorm (H s) x) ^ 2)
      (D.laplacian (fun y => (g.tensorNorm (H t) y) ^ 2) x +
        4 * (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ p, ∑ q, H t x (fun i => b (a i)) *
            D.curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q) *
              H t x ![b p, b q]) -
        2 * (g.tensorNorm (D.covariantTensorDerivative (H t)) x) ^ 2) t := by
  classical
  let b := (F.metric t).orthonormalBasis x
  have hupdate (a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)))
      (j : Fin 2) (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      Function.update (fun i => b (a i)) j (b q) =
        (fun i => b (Function.update a j q i)) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  have hd := M04.hasDerivAt_flow_tensorNorm_sq F H hH ht x _ hheat
  apply hd.congr_deriv
  rw [M04.laplacian_tensorNorm_sq (F.connection t) (hH t)]
  have hcancel :
      (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ j : Fin 2, ∑ q,
          H t x (fun i => b (a i)) *
            ((F.connection t).ricci x (b (a j)) (b q) *
              H t x (fun i => b (Function.update a j q i)))) =
      (∑ j : Fin 2,
        ∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), ∑ q,
          (F.connection t).ricci x (b (a j)) (b q) *
            H t x (fun i => b (a i)) * H t x (fun i => b (Function.update a j q i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hcurv :
      (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ p, ∑ q, H t x (fun i => b (a i)) *
          (2 * ((F.connection t).curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q) *
            H t x ![b p, b q]))) =
      2 * (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ p, ∑ q, H t x (fun i => b (a i)) *
          (F.connection t).curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q) *
            H t x ![b p, b q]) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hsplit :
      (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        H t x (fun i => b (a i)) *
          ((F.connection t).tensorLaplacian (H t) x (fun i => b (a i)) +
            lichnerowiczReaction (F.connection t) (H t) x (fun i => b (a i)))) =
      M04.tensorPairing (F.metric t) (H t) ((F.connection t).tensorLaplacian (H t)) x +
        2 * (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ p, ∑ q, H t x (fun i => b (a i)) *
            (F.connection t).curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q) *
              H t x ![b p, b q]) -
        (∑ j : Fin 2,
          ∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), ∑ q,
            (F.connection t).ricci x (b (a j)) (b q) *
              H t x (fun i => b (a i)) * H t x (fun i => b (Function.update a j q i))) := by
    dsimp only [b] at hupdate hcancel hcurv ⊢
    conv_lhs => simp only [lichnerowiczReaction, mul_add, mul_sub, Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, hupdate]
    rw [hcancel, hcurv]
    simp only [M04.tensorPairing, add_sub_assoc]
  dsimp only [b] at hsplit
  rw [hsplit]
  ring




theorem lichnerowicz_curvature_pairing_le (D : LeviCivitaData g)
    {H : CovariantTensorEvaluation n M 2} (hH : IsSmoothCovariantTensor H)
    (x : M) {K : ℝ} (hK : 0 ≤ K) (hRm : D.curvatureTensorNorm x ≤ K) :
    (∑ a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
      ∑ p, ∑ q, H x (fun i => g.orthonormalBasis x (a i)) *
        D.curvatureTensor x (g.orthonormalBasis x (a 0)) (g.orthonormalBasis x p)
          (g.orthonormalBasis x (a 1)) (g.orthonormalBasis x q) *
            H x ![g.orthonormalBasis x p, g.orthonormalBasis x q]) ≤
      (n : ℝ) ^ 4 * K * (g.tensorNorm H x) ^ 2 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let N := g.tensorNorm H x
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hb (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
  have hHabs (a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      |H x (fun i => b (a i))| ≤ N := by
    have h := M04.tensorEvaluation_sq_le_tensorNorm g hH x (fun i => b (a i))
    simp only [hb, Finset.prod_const_one, mul_one] at h
    nlinarith only [h, hN, sq_abs (H x (fun i => b (a i))),
      abs_nonneg (H x (fun i => b (a i)))]
  have hRabs (i j k l) : |D.curvatureTensor x (b i) (b j) (b k) (b l)| ≤ K := by
    have h := M04.tensorEvaluation_sq_le_tensorNorm g
      (M04.isSmoothCovariantTensor_riemannEvaluation D) x ![b i, b j, b k, b l]
    have hn : g.tensorNorm D.riemannEvaluation x = D.curvatureTensorNorm x :=
      D.curvatureDerivativeNorm_zero x
    simp only [LeviCivitaData.riemannEvaluation, Fin.prod_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hb, one_mul, hn] at h
    have hnonneg : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
    have hle : |D.curvatureTensor x (b i) (b j) (b k) (b l)| ≤
        D.curvatureTensorNorm x := by
      nlinarith only [h, hnonneg, sq_abs (D.curvatureTensor x (b i) (b j) (b k) (b l)),
        abs_nonneg (D.curvatureTensor x (b i) (b j) (b k) (b l))]
    exact hle.trans hRm
  have hterm (a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) (p q) :
      H x (fun i => b (a i)) * D.curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q) *
        H x ![b p, b q] ≤ K * N ^ 2 := by
    have hpq : |H x ![b p, b q]| ≤ N := by
      have he : (fun i : Fin 2 => b (![p, q] i)) = ![b p, b q] := by
        ext i
        fin_cases i <;> rfl
      simpa only [he] using hHabs ![p, q]
    calc
      _ ≤ |H x (fun i => b (a i))| *
          |D.curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q)| * |H x ![b p, b q]| := by
        simpa only [abs_mul] using le_abs_self
          (H x (fun i => b (a i)) * D.curvatureTensor x (b (a 0)) (b p) (b (a 1)) (b q) *
            H x ![b p, b q])
      _ ≤ N * K * N := mul_le_mul
        (mul_le_mul (hHabs a) (hRabs _ _ _ _) (abs_nonneg _) hN) hpq
        (abs_nonneg _) (mul_nonneg hN hK)
      _ = K * N ^ 2 := by ring
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ _a : Fin 2 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _p : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), K * N ^ 2 :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun p _ =>
        Finset.sum_le_sum fun q _ => hterm a p q
    _ = _ := by simp [hdim, N, mul_assoc]; ring



theorem lichnerowicz_normSq_heat_le {J : Set ℝ} (F : RicciFlow n M J)
    (H : ℝ → CovariantTensorEvaluation n M 2)
    (hH : ∀ s, IsSmoothCovariantTensor (H s)) {t : ℝ} (ht : t ∈ interior J)
    (x : M) {K : ℝ} (hK : 0 ≤ K) (hRm : (F.connection t).curvatureTensorNorm x ≤ K)
    (hheat : ∀ v, HasDerivAt (fun s => H s x v)
      ((F.connection t).tensorLaplacian (H t) x v +
        lichnerowiczReaction (F.connection t) (H t) x v) t) :
    ∃ a : ℝ, HasDerivAt (fun s => ((F.metric s).tensorNorm (H s) x) ^ 2) a t ∧
      a ≤ (F.connection t).laplacian (fun y => ((F.metric t).tensorNorm (H t) y) ^ 2) x +
        (4 * (n : ℝ) ^ 4 * K) * ((F.metric t).tensorNorm (H t) x) ^ 2 := by
  refine ⟨_, hasDerivAt_lichnerowicz_normSq F H hH ht x hheat, ?_⟩
  have hbound := lichnerowicz_curvature_pairing_le (F.connection t) (hH t) x hK hRm
  nlinarith only [hbound, sq_nonneg ((F.metric t).tensorNorm
    ((F.connection t).covariantTensorDerivative (H t)) x)]

end PoincareConjecture.M35.Uniqueness
