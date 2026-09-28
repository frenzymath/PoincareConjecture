import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma contDiffAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {t : ℝ}
    (hf : ∀ v, ContDiffAt ℝ ∞ (fun s => f s v) t) :
    ContDiffAt ℝ ∞ f t := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp t
    (contDiffAt_pi.mpr fun i => hf _)

lemma hasDerivAt_covariantTensorEvaluation_update
    (F : RicciFlow n M J) {k : ℕ} {T W : ℝ → CovariantTensorEvaluation n M k}
    {t : ℝ} {x : M}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X : Fin k → (z : M) → TangentSpace (𝓡 n) z),
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, y))
    (hW : ∀ (y : M) (z : Fin k → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (v : Fin k → TangentSpace (𝓡 n) x) (i : Fin k)
    {V : ℝ → TangentSpace (𝓡 n) x} {V' : TangentSpace (𝓡 n) x}
    (hV : HasDerivAt V V' t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt (fun s => T s x (Function.update v i (V s)))
      (W t x (Function.update v i (V t)) + T t x (Function.update v i V')) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  choose B hB using fun s => (hT s).1 x
  let L : ℝ → TangentSpace (𝓡 n) x →L[ℝ] ℝ := fun s =>
    ((B s).toLinearMap v i).toContinuousLinearMap
  have hL (s : ℝ) (q : TangentSpace (𝓡 n) x) : L s q = T s x (Function.update v i q) :=
    (hB s _).symm
  have hLs : ContDiffAt ℝ ∞ L t := by
    apply contDiffAt_clm_of_apply
    intro q
    let X := fun j => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Function.update v i q j)
    have hX (j : Fin k) := FiberBundle.contMDiffAt_extend (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (k := ∞) (Function.update v i q j)
    have h := ((hreg x X hX).comp t
      (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt
    simpa only [Function.comp_def, id_eq, X, FiberBundle.extend_apply_self, hL] using h
  have hLd := (hLs.differentiableAt (by simp)).hasDerivAt
  have hfixed := hLd.clm_apply (hasDerivAt_const t (V t))
  have hcoef : (deriv L t) (V t) = W t x (Function.update v i (V t)) := by
    simpa only [map_zero, add_zero] using hfixed.unique
      ((hW x (Function.update v i (V t))).congr_of_eventuallyEq
        (Eventually.of_forall fun s => hL s (V t)))
  simpa only [hL, hcoef, add_comm] using hLd.clm_apply hV

lemma hasDerivAt_covariantTensorDerivative_time_all
    (F : RicciFlow n M J) {k : ℕ} {T W : ℝ → CovariantTensorEvaluation n M k}
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X : Fin k → (z : M) → TangentSpace (𝓡 n) z),
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, y))
    (hW : ∀ (y : M) (z : Fin k → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (u : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
      (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
    HasDerivAt (fun s => (F.connection s).covariantTensorDerivative (T s) x (Fin.cons u v))
      ((F.connection t).covariantTensorDerivative (W t) x (Fin.cons u v) -
        ∑ i, T t x (Function.update v i (A (v i) u))) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let X := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  have hX (i : Fin k) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) (v i)
  have hconn (i : Fin k) :=
    ((F.contDiffAt_connection ht (hX i)).differentiableAt (by simp)).hasDerivAt
  have hconnU (i : Fin k) := (hconn i).clm_apply (hasDerivAt_const t u)
  simp only [map_zero, add_zero] at hconnU
  have hraw := Poincare.Manifold.hasDerivAt_mvfderiv_time
    (hreg x X hX) (fun y => hW y (fun i => X i y)) u
  have hslot (i : Fin k) := F.hasDerivAt_covariantTensorEvaluation_update hT hreg hW v i (hconnU i)
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i _ => hslot i
  have h := hraw.sub hsum
  convert h using 1 <;> try rfl
  · funext s
    simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
      Pi.sub_apply, Finset.sum_apply, X]
  · simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
      Finset.sum_add_distrib, sub_sub, X]

end PoincareConjecture.RicciFlow
