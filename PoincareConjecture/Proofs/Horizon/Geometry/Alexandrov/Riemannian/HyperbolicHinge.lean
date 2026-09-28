import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.UpperSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.InitialSupport








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric.Alexandrov

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem cosh_distance_upper_comparison
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (u v : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x u v)
    (p : M) {σ : ℝ → M} {b q : ℝ} (hb : 0 < b)
    (hσ : g.IsGeodesicOn σ (Icc 0 b))
    (hspeed : ∀ t ∈ Icc 0 b,
      g.tangentNorm (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ t 1) = 1)
    (hmin : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      g.edist (σ s) (σ t) = ENNReal.ofReal |s - t|)
    {u : ℝ → ℝ} (htouch : u 0 = Real.cosh (g.edist p (σ 0)).toReal)
    (hupper : ∀ᶠ t in 𝓝 0, Real.cosh (g.edist p (σ t)).toReal ≤ u t)
    (hu : HasDerivAt u q 0) :
    Real.cosh (g.edist p (σ b)).toReal ≤
      Real.cosh (g.edist p (σ 0)).toReal * Real.cosh b + q * Real.sinh b := by
  have hσcont : ContinuousOn σ (Icc 0 b) := fun t ht =>
    (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hσ ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t => Real.cosh (g.edist p (σ t)).toReal) (Icc 0 b) :=
    Real.continuous_cosh.comp_continuousOn
      ((g.continuous_toReal_edist p).comp_continuousOn hσcont)
  apply Poincare.Alexandrov.hyperbolic_upper_comparison_of_approximate_upper_support
    hb hcont htouch hupper hu
  intro t ht ε hε
  have htcc : t ∈ Icc 0 b := ⟨ht.1.le, ht.2.le⟩
  by_cases hpx : p = σ t
  · refine ⟨fun s => Real.cosh (s - t), by fun_prop, ?_, ?_, ?_⟩
    · rw [hpx, hmin t htcc t htcc]
      simp
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [hpx, hmin t htcc s ⟨hs.1.le, hs.2.le⟩,
        ENNReal.toReal_ofReal (abs_nonneg _), abs_sub_comm t s, Real.cosh_abs]
    · have hfirst : deriv (fun s => Real.cosh (s - t)) =
          (fun s => Real.sinh (s - t)) := by
        funext s
        simpa using (((hasDerivAt_id s).sub_const t).cosh).deriv
      have hsecond : deriv (deriv (fun s => Real.cosh (s - t))) t = 1 := by
        rw [hfirst]
        simpa using (((hasDerivAt_id t).sub_const t).sinh).deriv
      rw [hsecond, hpx, hmin t htcc t htcc]
      simpa using hε.le
  · obtain ⟨v, hv, htouch, hmajor, hbound⟩ :=
      exists_cosh_distance_upper_support g D hcomplete hsec p hσ htcc hpx hε
    have hs : g.inner (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ t 1) = 1 :=
      Real.sqrt_eq_one.mp (hspeed t htcc)
    exact ⟨v, hv, htouch, hmajor, by simpa only [hs, mul_one] using hbound⟩



theorem hyperbolic_hinge
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (u v : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x u v)
    {γ σ : ℝ → M} {p : M} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hγ : g.IsGeodesicOn γ (Icc 0 a)) (hσ : g.IsGeodesicOn σ (Icc 0 b))
    (hγ0 : γ 0 = p) (hσ0 : σ 0 = p)
    (hσspeed : ∀ t ∈ Icc 0 b,
      g.tangentNorm (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ t 1) = 1)
    (hγmin : ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hσmin : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      g.edist (σ s) (σ t) = ENNReal.ofReal |s - t|) :
    Real.cosh (g.edist (γ a) (σ b)).toReal ≤
      Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b *
        g.inner p (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let η : ℝ → M := fun t => γ (-a * t + a)
  have hη0 : η 0 = γ a := by simp [η]
  have hη1 : η 1 = p := by simp [η, hγ0]
  have hparam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : -a * t + a ∈ Icc 0 a :=
    ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  have hη : g.IsGeodesicOn η (Icc 0 1) :=
    fun t ht => hγ.comp_affine (-a) a t (hparam ht)
  have hdist : g.edist (η 0) (η 1) = ENNReal.ofReal a := by
    change g.edist (γ (-a * 0 + a)) (γ (-a * 1 + a)) = _
    norm_num only [mul_zero, zero_add, mul_one, neg_add_cancel]
    rw [hγmin a ⟨ha.le, le_rfl⟩ 0 ⟨le_rfl, ha.le⟩, sub_zero, abs_of_pos ha]
  have hneq : η 0 ≠ η 1 := by
    intro h
    have hself : g.edist (η 0) (η 1) = 0 := by
      rw [h]
      exact Manifold.riemannianEDist_self
    have := ENNReal.ofReal_pos.mpr ha
    rw [← hdist, hself] at this
    exact lt_irrefl _ this
  have hηmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist (η 0) (η 1) := by
    intro s hs t ht
    change g.edist (γ (-a * s + a)) (γ (-a * t + a)) = _
    rw [hγmin _ (hparam hs) _ (hparam ht), hdist,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [show -a * s + a - (-a * t + a) = -a * (s - t) by ring,
      abs_mul, abs_neg, abs_of_pos ha]
    ring
  have hσsmooth := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hσ
    (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.le⟩)
  obtain ⟨u, htouch, hupper, hu⟩ :=
    g.exists_cosh_distance_endpoint_support D hcomplete hη hneq hηmin
      hσsmooth (hσ0.trans hη1.symm)
  have hηvel : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1 =
      (-a) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 := by
    have hf : HasDerivAt (fun t : ℝ => -a * t + a) (-a) 1 := by
      convert! ((hasDerivAt_id (1 : ℝ)).const_mul (-a)).add_const a using 1
      simp
    have hγd := (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ
      (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.le⟩)).mdifferentiableAt (by simp)
    have hc := curve_velocity_comp (by simpa using hγd) hf
    have hv := congrArg (fun t : ℝ =>
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1))
      (show -a * 1 + a = 0 by ring)
    exact hc.trans (congrArg (fun z : EuclideanSpace ℝ (Fin n) => (-a) • z) hv)
  let q := g.inner p (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)
  have huderiv : HasDerivAt u (-Real.sinh a * q) 0 := by
    have hcoef : Real.sinh (g.edist (η 0) (η 1)).toReal /
          (g.edist (η 0) (η 1)).toReal *
          g.inner (η 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1) = -Real.sinh a * q := by
      rw [hdist, ENNReal.toReal_ofReal ha.le, hηvel, map_smul, smul_apply, smul_eq_mul]
      have hi := congrArg (fun x : M => g.inner x
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) hη1
      rw [hi]
      dsimp [q]
      field_simp [ha.ne']
    exact hcoef ▸ hu
  have hzero : Real.cosh (g.edist (γ a) (σ 0)).toReal = Real.cosh a := by
    rw [hσ0, ← hγ0, hγmin a ⟨ha.le, le_rfl⟩ 0 ⟨le_rfl, ha.le⟩,
      sub_zero, abs_of_pos ha, ENNReal.toReal_ofReal ha.le]
  have h := cosh_distance_upper_comparison g D hcomplete hsec (γ a) hb hσ
    hσspeed hσmin (by simpa only [hη0] using htouch)
    (by simpa only [hη0] using hupper) huderiv
  rw [hzero] at h
  dsimp [q] at h
  nlinarith

end PoincareConjecture.RiemannianMetric.Alexandrov
