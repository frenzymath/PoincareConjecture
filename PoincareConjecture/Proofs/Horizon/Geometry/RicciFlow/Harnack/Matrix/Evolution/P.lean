import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Derivatives
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Product
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.Antisymmetrization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.ReactionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Laplacian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Reaction.P
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

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

private lemma hasDerivAt_ricci_moving_left
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∀ {V : ℝ → TangentSpace (𝓡 n) x} {V' : TangentSpace (𝓡 n) x},
      HasDerivAt V V' t → ∀ w : TangentSpace (𝓡 n) x,
      HasDerivAt (fun s => (F.connection s).ricci x (V s) w)
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![V t, w] +
          (F.connection t).ricciReaction x (V t) w + (F.connection t).ricci x V' w) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  intro V V' hV w
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  choose A hA using fun s => (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.1.1 x
  let L : ℝ → TangentSpace (𝓡 n) x →L[ℝ] ℝ := fun s =>
    ((A s).toLinearMap ![0, w] 0).toContinuousLinearMap
  have hL (s : ℝ) (v : TangentSpace (𝓡 n) x) : L s v = (F.connection s).ricci x v w := by
    have he : Function.update ![0, w] 0 v = ![v, w] := by
      ext i
      fin_cases i <;> simp
    simpa [L, he, LeviCivitaData.ricciEvaluation] using (hA s ![v, w]).symm
  have hLs : ContDiffAt ℝ ∞ L t := by
    apply contDiffAt_clm_of_apply
    intro v
    have hv := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) v
    have hw := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) w
    have h := (F.contMDiffAt_ricci_fields ht hv hw).comp t
      (contMDiffAt_id.prodMk contMDiffAt_const)
    simpa only [Function.comp_def, id_eq, FiberBundle.extend_apply_self, hL] using h.contDiffAt
  have hLd := (hLs.differentiableAt (by simp)).hasDerivAt
  have hfixed := hLd.clm_apply (hasDerivAt_const t (V t))
  have he := hfixed.unique (by
    simpa only [hL] using
      (hC.ricci_evolution n M J F t (interior_subset ht) x (V t) w).hasDerivAt
        (mem_interior_iff_mem_nhds.mp ht))
  have h := hLd.clm_apply hV
  simp only [map_zero, add_zero] at he
  simpa only [hL, he, add_comm] using h

private lemma ricci_evolution_symm
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] +
        (F.connection t).ricciReaction x v w =
      (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![w, v] +
        (F.connection t).ricciReaction x w v := by
  have hs (s : ℝ) : (F.connection s).ricci x v w = (F.connection s).ricci x w v :=
    ((hC.tensor_calculus n M (F.metric s) (F.connection s)).2.2.2.1 x v w v w).2.2.2
  have hv := (hC.ricci_evolution n M J F t (interior_subset ht) x v w).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hw := (hC.ricci_evolution n M J F t (interior_subset ht) x w v).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  exact hv.unique (by simpa only [hs] using hw)

private lemma hasDerivAt_ricci_moving_right
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∀ {V : ℝ → TangentSpace (𝓡 n) x} {V' : TangentSpace (𝓡 n) x},
      HasDerivAt V V' t → ∀ w : TangentSpace (𝓡 n) x,
      HasDerivAt (fun s => (F.connection s).ricci x w (V s))
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![w, V t] +
          (F.connection t).ricciReaction x w (V t) + (F.connection t).ricci x w V') t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  intro V V' hV w
  have hs (s : ℝ) (v : TangentSpace (𝓡 n) x) :
      (F.connection s).ricci x v w = (F.connection s).ricci x w v :=
    ((hC.tensor_calculus n M (F.metric s) (F.connection s)).2.2.2.1 x v w v w).2.2.2
  simpa only [hs, ricci_evolution_symm hC F ht x (V t) w] using
    hasDerivAt_ricci_moving_left hC F ht x hV w



lemma hasDerivAt_covariantRicciDerivative
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let S : CovariantTensorEvaluation n M 2 := fun y z =>
      (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation y z +
        (F.connection t).ricciReaction y (z 0) (z 1)
    let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
      (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
    HasDerivAt (fun s =>
      (F.connection s).covariantTensorDerivative (F.connection s).ricciEvaluation x ![u, v, w])
      ((F.connection t).covariantTensorDerivative S x ![u, v, w] -
        (F.connection t).ricci x (A v u) w - (F.connection t).ricci x v (A w u)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let X := fun z : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z
  have hX (z : TangentSpace (𝓡 n) x) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) z
  have hconn (z : TangentSpace (𝓡 n) x) :=
    ((F.contDiffAt_connection ht (hX z)).differentiableAt (by simp)).hasDerivAt
  have hconnU (z : TangentSpace (𝓡 n) x) := (hconn z).clm_apply (hasDerivAt_const t u)
  simp only [map_zero, add_zero] at hconnU
  have hl := hasDerivAt_ricci_moving_left hC F ht x (hconnU v) w
  have hr := hasDerivAt_ricci_moving_right hC F ht x (hconnU w) v
  have hraw := PoincareConjecture.RicciFlow.hasDerivAt_mvfderiv_ricci_fields hC F ht (hX v) (hX w) u
  have h := hraw.sub (hl.add hr)
  have heval (y : M) :
      (fun i : Fin 2 => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (![v, w] i) y) =
        ![X v y, X w y] := by
    ext i
    fin_cases i <;> rfl
  have hup0 (a b c : TangentSpace (𝓡 n) x) :
      Function.update ![a, b] 0 c = ![c, b] := by
    ext i
    fin_cases i <;> simp
  have hup1 (a b c : TangentSpace (𝓡 n) x) :
      Function.update ![a, b] 1 c = ![a, c] := by
    ext i
    fin_cases i <;> simp
  convert h using 1 <;> try rfl
  · funext s
    simp [LeviCivitaData.covariantTensorDerivative, LeviCivitaData.ricciEvaluation,
      Fin.sum_univ_two]
  · simp [LeviCivitaData.covariantTensorDerivative, Fin.sum_univ_two, heval, hup0, hup1, X]
    ring



lemma hasDerivAt_hamiltonP_connection_corrected
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let S : CovariantTensorEvaluation n M 2 := fun y z =>
      (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation y z +
        (F.connection t).ricciReaction y (z 0) (z 1)
    let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
      (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
    HasDerivAt (fun s => hamiltonP (F.connection s) x u v w)
      ((F.connection t).covariantTensorDerivative S x ![u, v, w] -
        (F.connection t).covariantTensorDerivative S x ![v, u, w] -
        (F.connection t).ricci x v (A w u) + (F.connection t).ricci x u (A w v)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
    (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
  have hD := hC.tensor_calculus n M (F.metric t) (F.connection t)
  have hA : A v u = A u v := by
    apply ext_inner_right ℝ
    intro z
    change (F.metric t).inner x (A v u) z = (F.metric t).inner x (A u v) z
    dsimp only [A]
    rw [F.inner_deriv_connection_extend ht hD, F.inner_deriv_connection_extend ht hD,
      (F.connection t).covariantTensorDerivative_ricciEvaluation_symm hD x z v u]
    ring
  have h := (hasDerivAt_covariantRicciDerivative hC F ht x u v w).sub
    (hasDerivAt_covariantRicciDerivative hC F ht x v u w)
  change HasDerivAt _ _ t at h ⊢
  convert h using 1 <;> try rfl
  dsimp only
  rw [show A v u = A u v from hA]
  ring

private lemma ricci_deriv_connection_eq_sum
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    D.ricci x v ((deriv (fun s => (F.connection s).connection
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x) t) u) =
      ∑ i, D.ricci x v (b i) *
        (-D.covariantTensorDerivative D.ricciEvaluation x ![u, w, b i] -
          D.covariantTensorDerivative D.ricciEvaluation x ![w, u, b i] +
          D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, w]) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let z := (deriv (fun s => (F.connection s).connection
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x) t) u
  have hD := hC.tensor_calculus n M (F.metric t) D
  obtain ⟨A, hA⟩ := hD.2.1.1 x
  let L := bilinearOfTwoTensor A v
  have hL (a : TangentSpace (𝓡 n) x) : L a = D.ricci x v a := (hA ![v, a]).symm
  have hz := congrArg L (b.sum_repr' z)
  simp only [map_sum, map_smul, smul_eq_mul] at hz
  simp only [hL] at hz
  dsimp only
  rw [← hz]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]
  change (F.metric t).inner x z (b i) * D.ricci x v (b i) = _
  dsimp only [z]
  rw [F.inner_deriv_connection_extend ht hD]
  ring



lemma hasDerivAt_hamiltonP_connection_contractions
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let S : CovariantTensorEvaluation n M 2 := fun y z =>
      D.tensorLaplacian D.ricciEvaluation y z + D.ricciReaction y (z 0) (z 1)
    HasDerivAt (fun s => hamiltonP (F.connection s) x u v w)
      (D.covariantTensorDerivative S x ![u, v, w] -
        D.covariantTensorDerivative S x ![v, u, w] -
        (∑ i, D.ricci x v (b i) *
          (-D.covariantTensorDerivative D.ricciEvaluation x ![u, w, b i] -
            D.covariantTensorDerivative D.ricciEvaluation x ![w, u, b i] +
            D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, w])) +
        (∑ i, D.ricci x u (b i) *
          (-D.covariantTensorDerivative D.ricciEvaluation x ![v, w, b i] -
            D.covariantTensorDerivative D.ricciEvaluation x ![w, v, b i] +
            D.covariantTensorDerivative D.ricciEvaluation x ![b i, v, w]))) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have h := hasDerivAt_hamiltonP_connection_corrected hC F ht x u v w
  dsimp only at h ⊢
  rwa [ricci_deriv_connection_eq_sum hC F ht x u v w,
    ricci_deriv_connection_eq_sum hC F ht x v u w] at h


lemma tensorLaplacian_hamiltonP
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![u, v, w] =
      D.tensorLaplacian (D.covariantTensorDerivative D.ricciEvaluation) x ![u, v, w] -
        D.tensorLaplacian (D.covariantTensorDerivative D.ricciEvaluation) x ![v, u, w] := by
  let A := D.covariantTensorDerivative D.ricciEvaluation
  let B := D.covariantTensorDerivative A
  have hA := hD.2.2.1 2 D.ricciEvaluation hD.2.1
  have hB := hD.2.2.1 3 A hA
  have hfirst : D.covariantTensorDerivative
      (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) =
      fun y z => B y z - B y (z ∘ Equiv.swap 1 2) := by
    funext y z
    have hz : ![z 0, z 1, z 2, z 3] = z := by
      ext i
      fin_cases i <;> rfl
    have hswap : ![z 0, z 2, z 1, z 3] = z ∘ Equiv.swap 1 2 := by
      ext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [hz, hswap] using
      covariantTensorDerivative_hamiltonP D hD y (z 0) (z 1) (z 2) (z 3)
  have hsecond (a b : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative (D.covariantTensorDerivative
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2))) x ![a, b, u, v, w] =
      D.covariantTensorDerivative B x ![a, b, u, v, w] -
        D.covariantTensorDerivative B x ![a, b, v, u, w] := by
    rw [hfirst, D.covariantTensorDerivative_sub hB (hB.perm (Equiv.swap 1 2))]
    dsimp only
    rw [D.covariantTensorDerivative_reindex B (Equiv.swap 1 2) x ![a, b, u, v, w]]
    congr 2
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def] <;> rfl
  simp only [LeviCivitaData.tensorLaplacian, LeviCivitaData.iteratedCovariantTensorDerivative,
    Matrix.Fin.cons_vecCons]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => hsecond _ _)

private lemma covariantRicciDerivative_heat_reaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let S : CovariantTensorEvaluation n M 2 := fun y z =>
      D.tensorLaplacian D.ricciEvaluation y z + D.ricciReaction y (z 0) (z 1)
    D.covariantTensorDerivative S x ![u, v, w] -
      (∑ i, D.ricci x w (b i) *
        (-D.covariantTensorDerivative D.ricciEvaluation x ![u, v, b i] -
          D.covariantTensorDerivative D.ricciEvaluation x ![v, u, b i] +
          D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, v])) -
      (∑ i, D.ricci x v (b i) *
        (-D.covariantTensorDerivative D.ricciEvaluation x ![u, w, b i] -
          D.covariantTensorDerivative D.ricciEvaluation x ![w, u, b i] +
          D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, w])) =
      D.tensorLaplacian (D.covariantTensorDerivative D.ricciEvaluation) x ![u, v, w] +
        hamiltonPPreAntisym D x u v w -
        ∑ i, (D.ricci x u (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![b i, v, w] +
          D.ricci x v (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![u, b i, w] +
          D.ricci x w (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![u, v, b i]) := by
  have hL : IsSmoothCovariantTensor (D.tensorLaplacian D.ricciEvaluation) :=
    (hD.2.2.1 _ _ (hD.2.2.1 _ _ hD.2.1)).tensorTrace
  dsimp only
  rw [D.covariantTensorDerivative_add hL (D.isSmoothCovariantTensor_ricciReaction hD)]
  dsimp only
  rw [D.covariantTensorDerivative_ricciReaction hD]
  have hc := D.covariantTensorDerivative_tensorLaplacian_commutator_two hD hD.2.1 x u v w
  dsimp only at hc
  have heval (p q : TangentSpace (𝓡 n) x) :
      D.ricciEvaluation x ![p, q] = D.ricci x p q := rfl
  simp_rw [heval] at hc
  have hr (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.ricci x (g.orthonormalBasis x i) w = D.ricci x w (g.orthonormalBasis x i) :=
    (hD.2.2.2.1 x (g.orthonormalBasis x i) w u v).2.2.2
  have hs (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.covariantTensorDerivative D.ricciEvaluation x ![u, w, g.orthonormalBasis x i] =
        D.covariantTensorDerivative D.ricciEvaluation x ![u, g.orthonormalBasis x i, w] :=
    D.covariantTensorDerivative_ricciEvaluation_symm hD x u w (g.orthonormalBasis x i)
  simp_rw [hr, hs] at hc ⊢
  have hmul (z : Fin 3 → TangentSpace (𝓡 n) x) (r : ℝ) :
      D.covariantTensorDerivative D.ricciEvaluation x z * r =
        r * D.covariantTensorDerivative D.ricciEvaluation x z := mul_comm _ _
  simp only [hamiltonPPreAntisym, mul_add, mul_sub, sub_mul, mul_neg,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hc ⊢
  simp_rw [hmul] at hc ⊢
  linear_combination hc



lemma hasDerivAt_covariantRicciDerivative_evolution
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => (F.connection s).covariantTensorDerivative
      (F.connection s).ricciEvaluation x ![u, v, w])
      (D.tensorLaplacian (D.covariantTensorDerivative D.ricciEvaluation) x ![u, v, w] +
        hamiltonPPreAntisym D x u v w -
        ∑ i, (D.ricci x u (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![b i, v, w] +
          D.ricci x v (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![u, b i, w] +
          D.ricci x w (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![u, v, b i])) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let A := fun z : TangentSpace (𝓡 n) x => deriv (fun s =>
    (F.connection s).connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) x) t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have h := hasDerivAt_covariantRicciDerivative hC F ht x u v w
  have hs : D.ricci x (A v u) w = D.ricci x w (A v u) :=
    (hD.2.2.2.1 x (A v u) w u v).2.2.2
  dsimp only at h ⊢
  rw [hs, ricci_deriv_connection_eq_sum hC F ht x u w v,
    ricci_deriv_connection_eq_sum hC F ht x u v w] at h
  exact h.congr_deriv (covariantRicciDerivative_heat_reaction D hD x u v w)







theorem hasDerivAt_hamiltonP_evolution
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => hamiltonP (F.connection s) x u v w)
      (D.tensorLaplacian (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![u, v, w] +
        2 * (∑ d, ∑ e, D.curvatureTensor x u (b d) v (b e) *
          hamiltonP D x (b d) (b e) w) +
        2 * (∑ d, ∑ e, D.curvatureTensor x u (b d) w (b e) *
          hamiltonP D x (b d) v (b e)) +
        2 * (∑ d, ∑ e, D.curvatureTensor x v (b d) w (b e) *
          hamiltonP D x u (b d) (b e)) -
        2 * (∑ d, ∑ e, D.ricci x (b d) (b e) *
          D.covariantTensorDerivative D.riemannEvaluation x ![b d, u, v, w, b e]) -
        ∑ i, (D.ricci x u (b i) * hamiltonP D x (b i) v w +
          D.ricci x v (b i) * hamiltonP D x u (b i) w +
          D.ricci x w (b i) * hamiltonP D x u v (b i))) t := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  have hD := hC.tensor_calculus n M (F.metric t) D
  have h := (hasDerivAt_covariantRicciDerivative_evolution hC F ht x u v w).sub
    (hasDerivAt_covariantRicciDerivative_evolution hC F ht x v u w)
  have hpre := hamiltonPPreAntisym_sub_swap D hD x u v w
  have hslots :
      (∑ i, (D.ricci x u (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![b i, v, w] +
        D.ricci x v (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![u, b i, w] +
        D.ricci x w (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![u, v, b i])) -
      (∑ i, (D.ricci x v (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![b i, u, w] +
        D.ricci x u (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![v, b i, w] +
        D.ricci x w (b i) * D.covariantTensorDerivative D.ricciEvaluation x ![v, u, b i])) =
      ∑ i, (D.ricci x u (b i) * hamiltonP D x (b i) v w +
        D.ricci x v (b i) * hamiltonP D x u (b i) w +
        D.ricci x w (b i) * hamiltonP D x u v (b i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hamiltonP]
    ring
  dsimp only at h ⊢
  convert h using 1 <;> try rfl
  rw [tensorLaplacian_hamiltonP D hD]
  simp only [Finset.sum_add_distrib] at hpre
  dsimp only [D, b] at hpre hslots
  linear_combination -hpre + hslots




theorem hamiltonP_covariant_evolution
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    deriv (fun s => hamiltonP (F.connection s) x u v w) t +
        (∑ i, (D.ricci x u (b i) * hamiltonP D x (b i) v w +
          D.ricci x v (b i) * hamiltonP D x u (b i) w +
          D.ricci x w (b i) * hamiltonP D x u v (b i))) -
        D.tensorLaplacian (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![u, v, w] =
      2 * (∑ d, ∑ e, D.curvatureTensor x u (b d) v (b e) * hamiltonP D x (b d) (b e) w) +
      2 * (∑ d, ∑ e, D.curvatureTensor x u (b d) w (b e) * hamiltonP D x (b d) v (b e)) +
      2 * (∑ d, ∑ e, D.curvatureTensor x v (b d) w (b e) * hamiltonP D x u (b d) (b e)) -
      2 * (∑ d, ∑ e, D.ricci x (b d) (b e) *
        D.covariantTensorDerivative D.riemannEvaluation x ![b d, u, v, w, b e]) := by
  have h := (hasDerivAt_hamiltonP_evolution hC F ht x u v w).deriv
  dsimp only at h ⊢
  linarith only [h]


lemma tensorHeatOperator_hamiltonP
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) :
    F.tensorHeatOperator (fun s y z => hamiltonP (F.connection s) y (z 0) (z 1) (z 2)) t =
      hamiltonPReaction (F.connection t) := by
  funext x z
  have hz : z = ![z 0, z 1, z 2] := by ext i; fin_cases i <;> rfl
  rw [hz]
  have h := hamiltonP_covariant_evolution hC F ht x (z 0) (z 1) (z 2)
  dsimp only at h
  unfold RicciFlow.tensorHeatOperator
  simp only [LeviCivitaData.ricciTensorAction, Fin.sum_univ_three,
    Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte,
    hamiltonPReaction, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [Finset.sum_add_distrib] at h
  exact h

end Poincare.RicciFlow.Harnack
