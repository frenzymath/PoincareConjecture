import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

universe u

namespace PoincareConjecture.RicciFlow

open PoincareConjecture

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

lemma hasDerivAt_covariantTensorEvaluation_moving_left
    (F : RicciFlow n M J) {T W : ℝ → CovariantTensorEvaluation n M 2}
    {t : ℝ} {x : M}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X Y : (z : M) → TangentSpace (𝓡 n) z),
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) y →
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) y →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 ![X p.2, Y p.2]) (t, y))
    (hW : ∀ (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (ht : t ∈ interior J) (u v w : TangentSpace (𝓡 n) x)
    {V : ℝ → TangentSpace (𝓡 n) x} {V' : TangentSpace (𝓡 n) x}
    (hV : HasDerivAt V V' t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt (fun s => T s x ![V s, w])
      (W t x ![V t, w] + T t x ![V', w]) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  choose B hB using fun s => (hT s).1 x
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) w
  let L : ℝ → (TangentSpace (𝓡 n) x) →L[ℝ] ℝ := fun s =>
    ((B s).toLinearMap ![0, w] 0).toContinuousLinearMap
  have hL (s : ℝ) (q : TangentSpace (𝓡 n) x) : L s q = T s x ![q, w] := by
    have hu : Function.update ![0, w] 0 q = ![q, w] := by ext i; fin_cases i <;> simp
    simpa [L, hu] using (hB s ![q, w]).symm
  have hLs : ContDiffAt ℝ ∞ L t := by
    apply contDiffAt_clm_of_apply
    intro q
    let Xq := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q
    have hXq := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) q
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) t :=
      contMDiffAt_id.prodMk contMDiffAt_const
    have h := (hreg x Xq Y hXq hY).comp t hp
    have hc := h.contDiffAt
    convert hc using 1 <;> ext s <;> simp [L, hL, Xq, Y,
      FiberBundle.extend_apply_self]
  have hLd := (hLs.differentiableAt (by simp)).hasDerivAt
  have hLfixed := hLd.clm_apply (hasDerivAt_const t (V t))
  have hW' := hW x ![V t, w]
  have hcoef : (deriv L t) (V t) = W t x ![V t, w] := by
    simpa only [map_zero, add_zero] using hLfixed.unique (hW'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp only [hL]))
  have htime := hLd.clm_apply hV
  simpa only [hL, hcoef, add_comm] using htime

lemma hasDerivAt_covariantTensorEvaluation_moving_right
    (F : RicciFlow n M J) {T W : ℝ → CovariantTensorEvaluation n M 2}
    {t : ℝ} {x : M}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X Y : (z : M) → TangentSpace (𝓡 n) z),
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) y →
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) y →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 ![X p.2, Y p.2]) (t, y))
    (hW : ∀ (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (ht : t ∈ interior J) (u v w : TangentSpace (𝓡 n) x)
    {V : ℝ → TangentSpace (𝓡 n) x} {V' : TangentSpace (𝓡 n) x}
    (hV : HasDerivAt V V' t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt (fun s => T s x ![w, V s])
      (W t x ![w, V t] + T t x ![w, V']) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  choose B hB using fun s => (hT s).1 x
  let L : ℝ → (TangentSpace (𝓡 n) x) →L[ℝ] ℝ := fun s =>
    ((B s).toLinearMap ![w, 0] 1).toContinuousLinearMap
  have hL (s : ℝ) (q : TangentSpace (𝓡 n) x) : L s q = T s x ![w, q] := by
    have hu : Function.update ![w, 0] 1 q = ![w, q] := by ext i; fin_cases i <;> simp
    simpa [L, hu] using (hB s ![w, q]).symm
  have hLs : ContDiffAt ℝ ∞ L t := by
    apply contDiffAt_clm_of_apply
    intro q
    let Yq := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) q
    have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) w
    have hYq := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) q
    have hp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
    have h := (hreg x X Yq hX hYq).comp t hp
    have hc := h.contDiffAt
    convert hc using 1 <;> ext s <;> simp [L, hL, X, Yq, FiberBundle.extend_apply_self]
  have hLd := (hLs.differentiableAt (by simp)).hasDerivAt
  have hLfixed := hLd.clm_apply (hasDerivAt_const t (V t))
  have hW' := hW x ![w, V t]
  have hcoef : (deriv L t) (V t) = W t x ![w, V t] := by
    simpa only [map_zero, add_zero] using hLfixed.unique (hW'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp only [hL]))
  have htime := hLd.clm_apply hV
  simpa only [hL, hcoef, add_comm] using htime

lemma hasDerivAt_covariantTensorDerivative_time
    (F : RicciFlow n M J) {T W : ℝ → CovariantTensorEvaluation n M 2}
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X Y : (z : M) → TangentSpace (𝓡 n) z),
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) y →
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) y →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 ![X p.2, Y p.2]) (t, y))
    (hW : ∀ (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
      (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
    HasDerivAt (fun s =>
      (F.connection s).covariantTensorDerivative (T s) x ![u, v, w])
      ((F.connection t).covariantTensorDerivative (W t) x ![u, v, w] -
        T t x ![A v u, w] - T t x ![v, A w u]) t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let X := fun z : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  have hX (z : TangentSpace (𝓡 n) x) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) z
  have hconn (z : TangentSpace (𝓡 n) x) :=
    ((F.contDiffAt_connection ht (hX z)).differentiableAt (by simp)).hasDerivAt
  have hconnU (z : TangentSpace (𝓡 n) x) := (hconn z).clm_apply (hasDerivAt_const t u)
  simp only [map_zero, add_zero] at hconnU
  have hraw := Poincare.Manifold.hasDerivAt_mvfderiv_time
    (hreg x (X v) (X w) (hX v) (hX w))
    (fun y => hW y ![X v y, X w y]) u
  have hl := hasDerivAt_covariantTensorEvaluation_moving_left F hT hreg hW ht u v w
    (V := fun s => (F.connection s).connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x u) (hconnU v)
  have hr := hasDerivAt_covariantTensorEvaluation_moving_right F hT hreg hW ht u w v
    (V := fun s => (F.connection s).connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x u) (hconnU w)
  have h := hraw.sub (hl.add hr)
  have hu0 (a b c : TangentSpace (𝓡 n) x) : Function.update ![a, b] 0 c = ![c, b] := by
    ext i; fin_cases i <;> simp
  have hu1 (a b c : TangentSpace (𝓡 n) x) : Function.update ![a, b] 1 c = ![a, c] := by
    ext i; fin_cases i <;> simp
  have heval (y : M) :
      (fun i : Fin 2 => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (![v, w] i) y) =
        ![X v y, X w y] := by
    ext i; fin_cases i <;> rfl
  convert h using 1 <;> try rfl
  · funext s
    simp [LeviCivitaData.covariantTensorDerivative, Fin.sum_univ_two, hu0, hu1, X, heval]
  · simp [LeviCivitaData.covariantTensorDerivative, Fin.sum_univ_two, hu0, hu1, X, heval]
    ring

end PoincareConjecture.RicciFlow
