import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Semiconcavity








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


theorem toponogov_hinge
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {γ σ : ℝ → M} {p : M} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hγ : g.IsGeodesicOn γ (Icc 0 a)) (hσ : g.IsGeodesicOn σ (Icc 0 b))
    (hγ0 : γ 0 = p) (hσ0 : σ 0 = p)
    (hσspeed : ∀ t ∈ Icc 0 b,
      g.tangentNorm (σ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ t 1) = 1)
    (hγmin : ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hσmin : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b,
      g.edist (σ s) (σ t) = ENNReal.ofReal |s - t|) :
    (g.edist (γ a) (σ b)).toReal ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b *
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
    g.exists_squared_distance_endpoint_support D hcomplete hη hneq hηmin
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
  have huderiv : HasDerivAt u (-2 * a * q) 0 := by
    have hcoef : 2 * g.inner (η 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1) = -2 * a * q := by
      rw [hηvel, map_smul, smul_apply, smul_eq_mul]
      have hi := congrArg (fun x : M => g.inner x
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) hη1
      rw [hi]
      dsimp [q]
      ring
    exact hcoef ▸ hu
  let F : ℝ → ℝ := fun t => (g.edist (γ a) (σ t)).toReal ^ 2
  have hzero : F 0 = a ^ 2 := by
    dsimp [F]
    rw [hσ0, ← hγ0, hγmin a ⟨ha.le, le_rfl⟩ 0 ⟨le_rfl, ha.le⟩,
      sub_zero, abs_of_pos ha, ENNReal.toReal_ofReal ha.le]
  have hconc := g.squared_distance_sub_sq_concave D hcomplete hsec (γ a)
    hσ hσspeed hσmin
  have hdefderiv : HasDerivAt (fun t => u t - t ^ 2) (-2 * a * q) 0 := by
    convert! huderiv.sub ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    simp
  have htouch' : u 0 - (0 : ℝ) ^ 2 = F 0 - (0 : ℝ) ^ 2 := by
    rw [htouch, hη0]
  have hupper' : ∀ᶠ t in 𝓝 0, F t - t ^ 2 ≤ u t - t ^ 2 := by
    filter_upwards [hupper] with t ht
    exact sub_le_sub_right (by simpa only [hη0] using ht) _
  have h := Poincare.Analysis.le_affine_of_concaveOn_of_upper_support hb
    hconc htouch' hupper' hdefderiv
  change F b - b ^ 2 ≤ F 0 - (0 : ℝ) ^ 2 + (-2 * a * q) * (b - 0) at h
  rw [hzero] at h
  change F b ≤ a ^ 2 + b ^ 2 - 2 * a * b * q
  nlinarith

end PoincareConjecture.RiemannianMetric
