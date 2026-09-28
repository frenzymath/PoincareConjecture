import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FamilyCellNormalization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SmoothLimit

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

theorem m65CurvatureTensorNorm_le_of_ambient_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Icc a b)} {K0 K1 K2 : ℝ}
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2) (hK0 : 0 ≤ K0)
    {t : ℝ} (ht : t ∈ Icc a b) (p : M) :
    (F.connection t).curvatureTensorNorm p ≤ (n : ℝ) ^ 2 * K0 := by
  classical
  let g := F.metric t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := g.orthonormalBasis p
  have he (i) : g.tangentNorm p (e i) = 1 := by
    change Real.sqrt (inner ℝ (e i) (e i)) = 1
    simp only [real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one, one_pow, Real.sqrt_one]
  have hentry (i j k l) :
      (F.connection t).curvatureTensor p (e i) (e j) (e k) (e l) ^ 2 ≤ K0 ^ 2 := by
    have h := bounds.riemann t ht p ![e i, e j, e k, e l] (by
      intro m
      fin_cases m <;> exact (he _).le)
    dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at h
    exact (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) h 2)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  have hsum : (∑ i, ∑ j, ∑ k, ∑ l,
      (F.connection t).curvatureTensor p (e i) (e j) (e k) (e l) ^ 2) ≤
        ((n : ℝ) ^ 2 * K0) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)),
          ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)),
          ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)),
          ∑ _l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)), K0 ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hentry i j k l
      _ = _ := by simp [hdim]; ring
  exact (Real.sqrt_le_sqrt hsum).trans_eq
    (Real.sqrt_sq (mul_nonneg (sq_nonneg _) hK0))

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

set_option maxHeartbeats 1200000 in

theorem m65FamilyCell_exists_smooth_limit (C : M63FamilyConclusion G Gamma zeta)
    (compact : IsCompact (univ : Set M))
    (circumference : ℕ → ℝ) (h : ∀ k, 0 < circumference k)
    (hlt : ∀ k, circumference k < 1)
    (hzero : Tendsto circumference atTop (𝓝 0)) (z : LoopTwoSphere)
    {r s ell : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b) (hell : 0 < ell)
    (hlength : ∀ k, ell ≤ m62Length (G.product (circumference k) (h k)).flow
      ((C.solutions (circumference k) (h k)).curve z) r)
    (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hjets : ∀ k t x, t ∈ Icc r s → ∀ i,
      m63CurvatureJetSquared (G.product (circumference k) (h k)).flow
        ((C.solutions (circumference k) (h k)).curve z) i t x ≤ B i) :
    ∃ phi : ℕ → (ℝ ≃o ℝ),
      (∀ k, phi k 0 = 0 ∧ (∀ x, phi k (x + curvePeriod) = phi k x + curvePeriod) ∧
        ContDiff ℝ ∞ (phi k : ℝ → ℝ) ∧ (∀ x, 0 < deriv (phi k : ℝ → ℝ) x)) ∧
      ∃ select : ℕ → ℕ, StrictMono select ∧ ∃ clim : ℝ → ℝ → M,
        (∀ t ∈ Ioo r s, ∀ x, Tendsto
          (fun k => ((C.solutions (circumference (select k)) (h (select k))).curve z
            (phi (select k) x) t).1) atTop (𝓝 (clim x t))) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞ (fun p => clim p.2 p.1) (Ioo r s ×ˢ univ) ∧
        (∀ t ∈ Ioo r s, ∀ x, clim (x + curvePeriod) t = clim x t) ∧
        (∀ t ∈ Ioo r s, ∀ x,
          curveVelocity (n := 3) (fun y => clim y t) x ≠ 0 ∧
          curveVelocity (n := 3) (fun q => clim x q) t = m62CurvatureVector F clim t x) ∧
        ∀ p ∈ Ioo r s ×ˢ (univ : Set ℝ), ∃ (q : M) (J U : Set ℝ),
          IsOpen J ∧ IsOpen U ∧ p.1 ∈ J ∧ p.2 ∈ U ∧ J ×ˢ U ⊆ Ioo r s ×ˢ univ ∧
          (∀ w ∈ J ×ˢ U, clim w.2 w.1 ∈ (chartAt LoopAmbient q).source) ∧
          ∀ i K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ i (fun w : ℝ × ℝ => (chartAt LoopAmbient q)
              (((C.solutions (circumference (select k)) (h (select k))).curve z
                (phi (select k) w.2) w.1).1)))
            (iteratedFDeriv ℝ i (fun w : ℝ × ℝ => (chartAt LoopAmbient q) (clim w.2 w.1)))
            atTop K := by
  obtain ⟨phi, hphi, hc, hinit, vmin, vmax, hvmin, hvmax, hspeed, hj, hslope⟩ :=
    m65FamilyCell_normalization_bounds C circumference h hlt hzero z hrs hsub hell
      hlength B hB hjets
  let c := fun k x t => (C.solutions (circumference k) (h k)).curve z (phi k x) t
  obtain ⟨select, hselect, clim, hpoint, hsmooth, hperiod, hgeom, hchart⟩ :=
    m65Projected_exists_smooth_curveShortening_limit compact
      (fun k => G.product (circumference k) (h k)) c hc hrs hsub
      (mul_nonneg (sq_nonneg (3 : ℝ)) G.nonnegative.1)
      (fun t ht p => m65CurvatureTensorNorm_le_of_ambient_bounds G.bounds G.nonnegative.1
        (Ioo_subset_Icc_self (hsub ht)) p)
      (fun k => m62Length (G.product (circumference k) (h k)).flow
        ((C.solutions (circumference k) (h k)).curve z) r / curvePeriod)
      hinit ⟨vmax, hvmax, fun k t x ht => (hspeed k t x ht).2⟩ hj hvmin
      (fun k t x ht => (hspeed k t x ht).1)
      (fun t ht x => hslope t (Ioo_subset_Icc_self ht) x)
  exact ⟨phi, hphi, select, hselect, clim, hpoint, hsmooth, hperiod,
    (fun t ht x => (hgeom t ht x).2), hchart⟩

end PoincareConjecture
