import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.MeanValue.UpperSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Initial
import Mathlib.Analysis.SpecialFunctions.Sqrt










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




theorem exists_distance_support_of_minimizing_direction
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {γ σ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hmin : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ σ 0) (hσ0 : σ 0 = γ 0) :
    ∃ u : ℝ → ℝ,
      u 0 = (g.edist (γ L) (σ 0)).toReal ∧
      (∀ᶠ s in 𝓝 0, (g.edist (γ L) (σ s)).toReal ≤ u s) ∧
      HasDerivAt u (-g.inner (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let η : ℝ → M := fun t => γ (-L * t + L)
  have hη0 : η 0 = γ L := by simp [η]
  have hη1 : η 1 = γ 0 := by simp [η]
  have hparam {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : -L * t + L ∈ Icc 0 L :=
    ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  have hη : g.IsGeodesicOn η (Icc 0 1) :=
    fun t ht => hγ.comp_affine (-L) L t (hparam ht)
  have hdist : g.edist (η 0) (η 1) = ENNReal.ofReal L := by
    rw [hη0, hη1, hmin L ⟨hL.le, le_rfl⟩ 0 ⟨le_rfl, hL.le⟩,
      sub_zero, abs_of_pos hL]
  have hneq : η 0 ≠ η 1 := by
    intro h
    have hself : g.edist (η 0) (η 1) = 0 := by
      rw [h]
      exact Manifold.riemannianEDist_self
    have := ENNReal.ofReal_pos.mpr hL
    rw [← hdist, hself] at this
    exact lt_irrefl _ this
  have hηmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist (η 0) (η 1) := by
    intro s hs t ht
    change g.edist (γ (-L * s + L)) (γ (-L * t + L)) = _
    rw [hmin _ (hparam hs) _ (hparam ht), hdist,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [show -L * s + L - (-L * t + L) = -L * (s - t) by ring,
      abs_mul, abs_neg, abs_of_pos hL]
    ring
  obtain ⟨u, htouch, hupper, hu⟩ :=
    g.exists_squared_distance_endpoint_support D hc hη hneq hηmin
      hσ (hσ0.trans hη1.symm)
  have hηvel : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1 =
      (-L) • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 := by
    have hf : HasDerivAt (fun t : ℝ => -L * t + L) (-L) 1 := by
      convert! ((hasDerivAt_id (1 : ℝ)).const_mul (-L)).add_const L using 1
      simp
    have hγd := (hγ.contMDiffAt (show (0 : ℝ) ∈ Icc 0 L from
      ⟨le_rfl, hL.le⟩)).mdifferentiableAt (by simp)
    have hc := curve_velocity_comp (by simpa using hγd) hf
    have hv := congrArg (fun t : ℝ =>
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1))
      (show -L * 1 + L = 0 by ring)
    exact hc.trans (congrArg (fun z : EuclideanSpace ℝ (Fin n) => (-L) • z) hv)
  have hdistance : (g.edist (γ L) (σ 0)).toReal = L := by
    rw [hσ0, ← hη0, ← hη1, hdist, ENNReal.toReal_ofReal hL.le]
  have hu0 : u 0 = L ^ 2 := by
    rw [hη0, hdistance] at htouch
    exact htouch
  have hsqrt : Real.sqrt (u 0) = L := by rw [hu0, Real.sqrt_sq hL.le]
  refine ⟨fun s => Real.sqrt (u s), ?_, ?_, ?_⟩
  · exact hsqrt.trans hdistance.symm
  · filter_upwards [hupper] with s hs
    rw [hη0] at hs
    have hb := Real.sqrt_le_sqrt hs
    simpa only [Real.sqrt_sq ENNReal.toReal_nonneg] using hb
  · have hd := hu.sqrt (by rw [hu0]; positivity)
    have hcoef : (2 * g.inner (η 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 1 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) / (2 * Real.sqrt (u 0)) =
        -g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1) := by
      rw [hηvel, map_smul, smul_apply, smul_eq_mul, hsqrt]
      have hi := congrArg (fun x : M => g.inner x
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)) hη1
      rw [hi]
      field_simp
    exact hcoef ▸ hd




theorem edist_increment_ge_of_inward_pairing_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {c : ℝ → M} {p : M} {a b κ : ℝ}
    (hab : a ≤ b)
    (hcsm : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c t)
    (haway : ∀ t ∈ Icc a b, c t ≠ p)
    (hinward : ∀ t ∈ Icc a b, ∀ γ : ℝ → M,
      g.IsGeodesicOn γ (Icc 0 (g.edist (c t) p).toReal) →
      γ 0 = c t → γ (g.edist (c t) p).toReal = p →
      (∀ s ∈ Icc 0 (g.edist (c t) p).toReal,
        g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = 1) →
      (∀ s ∈ Icc 0 (g.edist (c t) p).toReal,
        ∀ u ∈ Icc 0 (g.edist (c t) p).toReal,
          g.edist (γ s) (γ u) = ENNReal.ofReal |s - u|) →
      g.inner (c t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ≤ -κ) :
    κ * (b - a) ≤ (g.edist p (c b)).toReal - (g.edist p (c a)).toReal := by
  let : MetricSpace M := g.toMetricSpace
  have hcont : ContinuousOn (fun t : ℝ => (g.edist p (c (-t))).toReal)
      (Icc (-b) (-a)) := by
    intro t ht
    have ht' : -t ∈ Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hcc : ContinuousAt (fun t : ℝ => c (-t)) t :=
      (hcsm _ ht').continuousAt.comp (by fun_prop)
    exact ((g.continuous_toReal_edist p).continuousAt.comp hcc).continuousWithinAt
  have hb := Poincare.Analysis.sub_le_mul_sub_of_hasDerivAt_upper_support
    (neg_le_neg hab) hcont (C := -κ) (fun t ht => ?_)
  · simp only [neg_neg] at hb
    nlinarith only [hb]
  have ht' : -t ∈ Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hL : 0 < (g.edist (c (-t)) p).toReal := by
    exact ENNReal.toReal_pos (edist_pos.mpr (haway _ ht')).ne'
      (g.edist_ne_top _ _)
  obtain ⟨γ, hγ0, hγL, hγ, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc (c (-t)) p hL
  let σ : ℝ → M := fun s => c (-(t + s))
  have hσ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ σ 0 := by
    have haff : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => -(t + s)) 0 := by
      apply contMDiffAt_iff_contDiffAt.mpr
      fun_prop
    have hcs : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c (-(t + 0)) := by
      simpa only [add_zero] using hcsm (-t) ht'
    exact hcs.comp 0 haff
  have hσ0 : σ 0 = γ 0 := by simpa only [σ, add_zero] using hγ0.symm
  obtain ⟨u, hu0, hupper, hu⟩ :=
    g.exists_distance_support_of_minimizing_direction D hc hL hγ hmin hσ hσ0
  have hσvel : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1 =
      -mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (-t) 1 := by
    have haff : HasDerivAt (fun s : ℝ => -(t + s)) (-1) 0 := by
      convert! ((hasDerivAt_id (0 : ℝ)).add_const t).neg using 1
      ext s
      simp only [Pi.neg_apply, id_eq, add_comm]
    have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) c (-(t + 0)) := by
      simpa only [add_zero] using (hcsm (-t) ht').mdifferentiableAt (by simp)
    have hd := curve_velocity_comp (γ := c) (f := fun s : ℝ => -(t + s))
      (t := 0) hcd haff
    have hv := congrArg (fun s : ℝ =>
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c s 1))
      (show -(t + 0) = -t by simp)
    exact hd.trans ((congrArg (fun z : EuclideanSpace ℝ (Fin n) => (-1 : ℝ) • z)
      hv).trans (neg_one_smul ℝ _))
  let d := -g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) σ 0 1)
  refine ⟨fun s => u (s - t), d, ?_, ?_, ?_, ?_⟩
  · have hd : HasDerivAt (fun s : ℝ => s - t) 1 t := by
      simpa using (hasDerivAt_id t).sub_const t
    have hcomp := hu.comp_of_eq t hd (by simp)
    simpa only [Function.comp_def, sub_self, mul_one] using hcomp
  · simpa only [sub_self, hγL, σ, add_zero] using hu0
  · have htend : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
      simpa using (show ContinuousAt (fun s : ℝ => s - t) t by fun_prop).tendsto
    filter_upwards [htend.eventually hupper] with s hs
    simpa only [hγL, σ, add_sub_cancel] using hs
  · dsimp [d]
    rw [hσvel, map_neg, neg_neg]
    have hi := g.symm (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (-t) 1)
    rw [hi]
    have hbase := congrArg (fun q : M => g.inner q
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c (-t) 1)
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1)) hγ0
    rw [hbase]
    exact hinward (-t) ht' γ hγ hγ0 hγL hspeed hmin

end PoincareConjecture.RiemannianMetric
