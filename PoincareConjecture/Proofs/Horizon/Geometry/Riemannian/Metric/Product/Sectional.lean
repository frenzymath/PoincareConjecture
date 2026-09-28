import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Traces
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Sectional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

private theorem exists_basis_adjoin
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] W) (hL : ∀ u v, ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ)
    (N : W) (hN : ⟪N, N⟫_ℝ = 1) (hNT : ∀ u, ⟪N, L u⟫_ℝ = 0)
    (hdim : Module.finrank ℝ W = Fintype.card ι + 1) :
    ∃ B : OrthonormalBasis (Option ι) ℝ W,
      B none = N ∧ ∀ i, B (some i) = L (b i) := by
  classical
  let v : Option ι → W := fun i => i.elim N (fun j => L (b j))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j => exact hNT (b j)
    | some i =>
      cases j with
      | none => exact (real_inner_comm _ _).trans (hNT (b i))
      | some j => simpa only [v, Option.elim_some, hL, Option.some.injEq]
          using b.inner_eq_ite i j
  have hcard : Fintype.card (Option ι) = Module.finrank ℝ W := by
    simpa using hdim.symm
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  have ha : Orthonormal ℝ a := by simpa [a] using hv
  refine ⟨a.toOrthonormalBasis ha, ?_, ?_⟩ <;> simp [a, v]

theorem PoincareConjecture.RiemannianMetric.FactorCurvature.sectional_lower_bound_of_null_normal
    {n : ℕ} {M S : Type*} [TopologicalSpace M] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 (n + 1)) ∞ M] [IsManifold (𝓡 n) ∞ S]
    {g : PoincareConjecture.RiemannianMetric (n + 1) M}
    {h : PoincareConjecture.RiemannianMetric n S}
    (D : PoincareConjecture.LeviCivitaData g) (Dh : PoincareConjecture.LeviCivitaData h) (x : M) (y : S)
    (L : TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 (n + 1)) x)
    (hL : ∀ u v, g.inner x (L u) (L v) = h.inner y u v)
    (ν : TangentSpace (𝓡 (n + 1)) x)
    (hν : g.inner x ν ν = 1) (hνT : ∀ u, g.inner x ν (L u) = 0)
    (hR : ∀ u v w z, Dh.curvatureTensor y u v w z =
      D.curvatureTensor x (L u) (L v) (L w) (L z))
    (hzero : ∀ u v w,
      D.curvatureTensor x ν u v w = 0 ∧ D.curvatureTensor x u ν v w = 0 ∧
      D.curvatureTensor x u v ν w = 0 ∧ D.curvatureTensor x u v w ν = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ u v : TangentSpace (𝓡 n) y, -K ≤ Dh.sectionalCurvature y u v) :
    ∀ u v : TangentSpace (𝓡 (n + 1)) x, -K ≤ D.sectionalCurvature x u v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : S → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := h.orthonormalBasis y
  obtain ⟨B, hB0, hBi⟩ := exists_basis_adjoin b L hL ν hν hνT (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) =
      Fintype.card (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) + 1
    simp)
  have decompose (u : TangentSpace (𝓡 (n + 1)) x) :
      ∃ a : TangentSpace (𝓡 n) y, ∃ s : ℝ, u = L a + s • ν := by
    refine ⟨∑ i, (B.repr u (some i)) • b i, B.repr u none, ?_⟩
    have hh := B.sum_repr u
    rw [Fintype.sum_option, hB0] at hh
    simp_rw [hBi] at hh
    rw [map_sum]
    simp only [map_smul]
    exact hh.symm.trans (add_comm _ _)
  intro u v
  obtain ⟨a,s,rfl⟩ := decompose u
  obtain ⟨b,t,rfl⟩ := decompose v
  have z₁ := fun u v w => (hzero u v w).1
  have z₂ := fun u v w => (hzero u v w).2.1
  have z₃ := fun u v w => (hzero u v w).2.2.1
  have z₄ := fun u v w => (hzero u v w).2.2.2
  have hcurv :
      D.curvatureTensor x (L a + s • ν) (L b + t • ν) (L a + s • ν) (L b + t • ν) =
        Dh.curvatureTensor y a b a b := by
    simp only [D.curvatureTensor_add_first, D.curvatureTensor_add_second,
      D.curvatureTensor_add_third, D.curvatureTensor_add_last,
      D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
      D.curvatureTensor_smul_third, D.curvatureTensor_smul_last,
      z₁, z₂, z₃, z₄, mul_zero, add_zero, hR]
  have hi (a b : TangentSpace (𝓡 n) y) (s t : ℝ) :
      g.inner x (L a + s • ν) (L b + t • ν) = h.inner y a b + s*t := by
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hL, hν, hνT, g.symm x (L a) ν, mul_zero, mul_one, zero_add, add_zero]
    ring
  let Δ := h.inner y a a * h.inner y b b - (h.inner y a b)^2
  let Γ := g.inner x (L a + s • ν) (L a + s • ν) *
      g.inner x (L b + t • ν) (L b + t • ν) -
        (g.inner x (L a + s • ν) (L b + t • ν))^2
  have hΔ : 0 ≤ Δ := by
    have hcs := real_inner_mul_inner_self_le a b
    change h.inner y a b * h.inner y a b ≤ h.inner y a a * h.inner y b b at hcs
    dsimp [Δ]
    nlinarith
  have hcompare : Δ ≤ Γ := by
    have hn : 0 ≤ inner ℝ (t • a - s • b) (t • a - s • b) := real_inner_self_nonneg
    change 0 ≤ h.inner y (t • a - s • b) (t • a - s • b) at hn
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
      h.symm y b a] at hn
    dsimp [Δ, Γ]
    rw [hi, hi, hi]
    nlinarith only [hn]
  have hΓ : 0 ≤ Γ := hΔ.trans hcompare
  have hlower : -K * Γ ≤ Dh.curvatureTensor y a b a b := by
    rw [Dh.curvatureTensor_diagonal_eq_sectional_mul_gram]
    change -K * Γ ≤ Dh.sectionalCurvature y a b * Δ
    exact (mul_le_mul_of_nonpos_left hcompare (neg_nonpos.mpr hK)).trans
      (mul_le_mul_of_nonneg_right (hsec a b) hΔ)
  by_cases hΓzero : Γ = 0
  · have hz := D.sectionalCurvature_eq_zero_of_gramDet_eq_zero x
      (L a + s • ν) (L b + t • ν) hΓzero
    rw [hz]
    linarith
  · unfold PoincareConjecture.LeviCivitaData.sectionalCurvature
    rw [hcurv]
    change -K ≤ Dh.curvatureTensor y a b a b / Γ
    exact (le_div_iff₀ (lt_of_le_of_ne hΓ (Ne.symm hΓzero))).mpr hlower
