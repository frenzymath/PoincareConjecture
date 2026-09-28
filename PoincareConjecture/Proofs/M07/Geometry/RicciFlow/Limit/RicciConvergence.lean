import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology
open Filter

namespace PoincareConjecture.LeviCivitaData

private def curvatureBilinear
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (u v : E) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  have h1 (a b c : E) : Function.update ![u, a, v, b] 1 c = ![u, c, v, b] := by
    ext i; fin_cases i <;> simp
  have h3 (a b c : E) : Function.update ![u, a, v, b] 3 c = ![u, a, v, c] := by
    ext i; fin_cases i <;> simp
  exact LinearMap.mk₂ ℝ (fun a b => A ![u, a, v, b])
    (fun a a' b => by simpa only [MultilinearMap.toLinearMap_apply, h1] using
      (A.toLinearMap ![u, a, v, b] 1).map_add a a')
    (fun c a b => by simpa only [MultilinearMap.toLinearMap_apply, h1] using
      (A.toLinearMap ![u, a, v, b] 1).map_smul c a)
    (fun a b b' => by simpa only [MultilinearMap.toLinearMap_apply, h3] using
      (A.toLinearMap ![u, a, v, b] 3).map_add b b')
    (fun c a b => by simpa only [MultilinearMap.toLinearMap_apply, h3] using
      (A.toLinearMap ![u, a, v, b] 3).map_smul c b)

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem ricci_eq_inverse_gram (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ)
    (hA : ∀ w, D.curvatureTensor x (w 0) (w 1) (w 2) (w 3) = A w)
    (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
        D.curvatureTensor x u (b i) v (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := bilinear_sum_basis_eq_inverse_gram (curvatureBilinear A u v)
    b (g.orthonormalBasis x)
  change (∑ i, A ![u, g.orthonormalBasis x i, v, g.orthonormalBasis x i]) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
      A ![u, b i, v, b j] at h
  simpa [← hA, ricci] using h


theorem ricci_eq_of_linearEquiv
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {h : RiemannianMetric n N} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (y : N)
    (e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) y)
    (hmetric : ∀ u v, h.inner y (e u) (e v) = g.inner x u v)
    (hcurv : ∀ u v w z, D'.curvatureTensor y (e u) (e v) (e w) (e z) =
      D.curvatureTensor x u v w z)
    (B : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) y) ℝ)
    (hB : ∀ w, D'.curvatureTensor y (w 0) (w 1) (w 2) (w 3) = B w)
    (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = D'.ricci y (e u) (e v) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner hmetric
  have hc := bilinear_sum_orthonormalBasis_eq (curvatureBilinear B (e u) (e v))
    ((g.orthonormalBasis x).map e') (h.orthonormalBasis y)
  change (∑ i, B ![e u, e (g.orthonormalBasis x i), e v,
    e (g.orthonormalBasis x i)]) =
      ∑ i, B ![e u, h.orthonormalBasis y i, e v, h.orthonormalBasis y i] at hc
  simpa [← hB, hcurv, ricci] using hc

end Manifold

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem tendsto_ricci_of_scalar_metric_jets
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ a, LeviCivitaData (gseq a)) (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a c : ι,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => (Dseq i).ricci x u v) l (𝓝 (D.ricci x u v)) := by
  classical
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x b h
  let Gseq : α → Matrix ι ι ℝ := fun a i j => (gseq a).inner x (b i) (b j)
  let G : Matrix ι ι ℝ := fun i j => g.inner x (b i) (b j)
  have hmatrix : Tendsto Gseq l (𝓝 G) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact ((ContinuousLinearMap.apply ℝ ℝ (b j)).continuous.continuousAt.tendsto.comp
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (b i)).continuous.continuousAt.tendsto.comp hzero))
  have hdet : G.det ≠ 0 := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change (Matrix.gram ℝ (show Module.Basis ι ℝ (TangentSpace (𝓡 n) x) from b)).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  have hinv : Tendsto (fun a => (Gseq a)⁻¹) l (𝓝 G⁻¹) := by
    apply (continuousAt_matrix_inv G ?_).tendsto.comp hmatrix
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet
  have heq (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (D' : LeviCivitaData g') :=
    D'.ricci_eq_inverse_gram x b (D'.exists_multilinear_curvatureTensor x).choose
      (D'.exists_multilinear_curvatureTensor x).choose_spec u v
  simp_rw [heq]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i)) j).mul
    (tendsto_curvatureTensor_of_metric_jets Dseq D x u (b i) v (b j) hzero hone htwo)


theorem ricci_eq_pullback_euclidean
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    {h : RiemannianMetric n N} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin n) → N} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (u v : EuclideanSpace ℝ (Fin n)) :
    D.ricci x u v = D'.ricci (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  obtain ⟨B, hB⟩ := D.exists_multilinear_curvatureTensor x
  have h := D'.ricci_eq_of_linearEquiv D (f x) x e.symm.toLinearEquiv
    (fun a b => by
      rw [hmetric.self_of_nhds, ← he]
      simp)
    (fun a b c d => by
      rw [D.curvatureTensor_eq_pullback_euclidean D' hf hinv hmetric, ← he]
      simp) B hB (e u) (e v)
  rw [← he]
  simpa using h.symm

end PoincareConjecture.LeviCivitaData
