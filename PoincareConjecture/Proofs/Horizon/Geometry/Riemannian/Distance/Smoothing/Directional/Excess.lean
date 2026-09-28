import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Derivative

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem distance_increment_on_minimizing_segment
    (g : RiemannianMetric n M) (p x q : M) {γ : ℝ → M}
    (hγ0 : γ 0 = x) (hγq : γ (g.edist x q).toReal = q)
    (hmin : ∀ s ∈ Icc (0 : ℝ) (g.edist x q).toReal,
      ∀ t ∈ Icc (0 : ℝ) (g.edist x q).toReal,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {T : ℝ} (hT : 0 ≤ T) (hTq : T ≤ (g.edist x q).toReal) :
    (∀ t ∈ Icc (0 : ℝ) T, (g.edist x (γ t)).toReal ≤ T) ∧
      T - ((g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal) ≤
        (g.edist p (γ T)).toReal - (g.edist p x).toReal := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (g.edist x q).toReal :=
    ⟨le_rfl, hT.trans hTq⟩
  have hTmem : T ∈ Icc (0 : ℝ) (g.edist x q).toReal := ⟨hT, hTq⟩
  constructor
  · intro t ht
    have heq := congrArg ENNReal.toReal (hmin 0 h0 t ⟨ht.1, ht.2.trans hTq⟩)
    simp only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1,
      ENNReal.toReal_ofReal ht.1] at heq
    exact heq.le.trans ht.2
  · have heq := congrArg ENNReal.toReal
      (hmin T hTmem (g.edist x q).toReal ⟨hT.trans hTq, le_rfl⟩)
    simp only [hγq, abs_of_nonpos (sub_nonpos.mpr hTq), neg_sub,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hTq)] at heq
    have htriangle := g.toReal_edist_triangle p (γ T) q
    linarith

theorem exists_opposite_witness_of_distance_approx
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (p x q : M) {T ε H : ℝ} (hT : 0 < T) (hTq : T ≤ (g.edist x q).toReal)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (herr : ∀ y, (g.edist x y).toReal ≤ T → |u y - (g.edist p y).toReal| ≤ ε)
    (hhess : ∀ y, (g.edist x y).toReal ≤ T → ∀ v : TangentSpace (𝓡 n) y,
      D.hessian u y v v ≤ H * g.inner y v v) :
    ∃ w : TangentSpace (𝓡 n) x, g.tangentNorm x w = 1 ∧
      g.inner x (D.gradient u x) w ≤
        -1 + ((g.edist p x).toReal + (g.edist x q).toReal -
          (g.edist p q).toReal + 2 * ε) / T + H * T / 2 := by
  obtain ⟨γ, hγ0, hγq, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc x q (hT.trans_le hTq)
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) (g.edist x q).toReal :=
    fun t ht => ⟨ht.1, ht.2.trans hTq⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  obtain ⟨hball, hincrement⟩ :=
    distance_increment_on_minimizing_segment g p x q hγ0 hγq hmin hT.le hTq
  let F : ℝ → ℝ := u ∘ γ
  let V := fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1
  let A := fun t => D.hessian u (γ t) (V t) (V t)
  let d := fun t => (g.edist p (γ t)).toReal
  let E := (g.edist p x).toReal + (g.edist x q).toReal - (g.edist p q).toReal
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt F (deriv F t) t := by
    apply DifferentiableAt.hasDerivAt
    apply (contMDiffAt_iff_contDiffAt.mp
      (((hu (γ t)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp t
        (hγ.contMDiffAt (hsub ht)))).differentiableAt (by simp)
  have hsecond (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      HasDerivAt (deriv F) (A t) t :=
    D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn isOpen_univ hu.contMDiffOn
      hγ (hsub ⟨ht.1.le, ht.2.le⟩) (mem_univ _)
  have hA (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : A t ≤ H := by
    have hunit : g.inner (γ t) (V t) (V t) = 1 :=
      Real.sqrt_eq_one.mp (hspeed t (hsub ⟨ht.1.le, ht.2.le⟩))
    have hb := hhess (γ t) (hball t ⟨ht.1.le, ht.2.le⟩) (V t)
    simpa only [hunit, mul_one] using hb
  have hlower : 1 - (E + 2 * ε) / T - H * T / 2 ≤ deriv F 0 := by
    apply Poincare.Analysis.deriv_lower_bound_of_endpoint_approx hT hfirst hsecond hA
      (d := d) (herr (γ 0) (hball 0 h0)) (herr (γ T) (hball T hlast))
    simpa only [d, E, hγ0] using hincrement
  let v : TangentSpace (𝓡 n) x := V 0
  have hv : g.tangentNorm x v = 1 := by
    have hv0 := hspeed 0 (hsub h0)
    change g.tangentNorm (γ 0) v = 1 at hv0
    rw [hγ0] at hv0
    exact hv0
  have hdu : deriv F 0 = mvfderiv (𝓡 n) u x v := by
    have heq := congrArg (fun L => L (1 : ℝ))
      (mfderiv_comp 0 ((hu (γ 0)).mdifferentiableAt (by simp))
        ((hγ.contMDiffAt (hsub h0)).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change deriv F 0 = mvfderiv (𝓡 n) u (γ 0) v at heq
    rw [hγ0] at heq
    exact heq
  refine ⟨-v, ?_, ?_⟩
  · simpa only [tangentNorm, map_neg, neg_apply, neg_neg] using hv
  · rw [map_neg, D.inner_gradient, ← hdu]
    dsimp only [E] at hlower
    linarith

theorem gradient_norm_lower_bound_of_distance_approx
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (p x q : M) {T ε H : ℝ} (hT : 0 < T) (hTq : T ≤ (g.edist x q).toReal)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (herr : ∀ y, (g.edist x y).toReal ≤ T → |u y - (g.edist p y).toReal| ≤ ε)
    (hhess : ∀ y, (g.edist x y).toReal ≤ T → ∀ v : TangentSpace (𝓡 n) y,
      D.hessian u y v v ≤ H * g.inner y v v) :
    1 - ((g.edist p x).toReal + (g.edist x q).toReal -
      (g.edist p q).toReal + 2 * ε) / T - H * T / 2 ≤
        g.tangentNorm x (D.gradient u x) := by
  obtain ⟨w, hw, hpair⟩ :=
    g.exists_opposite_witness_of_distance_approx D hc p x q hT hTq hu herr hhess
  have hcs := D.abs_mvfderiv_le_gradient_norm u x w
  rw [← D.inner_gradient, hw, mul_one] at hcs
  have habs := neg_le_abs (g.inner x (D.gradient u x) w)
  linarith

theorem mfderiv_ne_zero_of_distance_approx
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (p x q : M) {T ε H : ℝ} (hT : 0 < T) (hTq : T ≤ (g.edist x q).toReal)
    {u : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (herr : ∀ y, (g.edist x y).toReal ≤ T → |u y - (g.edist p y).toReal| ≤ ε)
    (hhess : ∀ y, (g.edist x y).toReal ≤ T → ∀ v : TangentSpace (𝓡 n) y,
      D.hessian u y v v ≤ H * g.inner y v v)
    (hsmall : ((g.edist p x).toReal + (g.edist x q).toReal -
      (g.edist p q).toReal + 2 * ε) / T + H * T / 2 < 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) u x ≠ 0 := by
  apply (g.tangentNorm_gradient_pos_iff u x).mp
  have hbound := g.gradient_norm_lower_bound_of_distance_approx D hc p x q hT hTq hu herr hhess
  change 0 < g.tangentNorm x (D.gradient u x)
  linarith

end PoincareConjecture.RiemannianMetric
