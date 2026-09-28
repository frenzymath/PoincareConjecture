import PoincareConjecture.Proofs.M28.Sec10_5_Angles.SquaredDistanceSupport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Global
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M28.Comparison

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem squared_distance_sub_sq_concave_of_cross_segments
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature)
    (p : M) {β : ℝ → M} {a b : ℝ}
    (hβ : g.IsGeodesicOn β (Icc a b))
    (hspeed : ∀ t ∈ Icc a b,
      g.tangentNorm (β t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β t 1) = 1)
    (hjoin : ∀ t ∈ Ioo a b, ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = β t ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ u) = ENNReal.ofReal
          (|s - u| * (g.edist p (β t)).toReal)) :
    ConcaveOn ℝ (Icc a b)
      (fun t => (g.edist p (β t)).toReal ^ 2 - t ^ 2) := by
  have hcont : ContinuousOn (fun t => (g.edist p (β t)).toReal ^ 2) (Icc a b) :=
    ((g.continuous_toReal_edist p).comp_continuousOn hβ.contMDiffOn.continuousOn).pow 2
  suffices h : ConcaveOn ℝ (Icc a b)
      (fun t => (g.edist p (β t)).toReal ^ 2 - 1 * t ^ 2) by
    simpa only [one_mul] using h
  apply Poincare.Analysis.concaveOn_sub_quadratic_of_approximate_upper_support hcont
  intro t ht epsilon hepsilon
  have htcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  let B : ℝ → M := fun s => β (s + t)
  have hB : g.IsGeodesicOn B {0} := by
    intro s hs
    have hs0 : s = 0 := hs
    subst s
    exact hβ.comp_add t 0 (by
      change 0 + t ∈ Icc a b
      simpa only [zero_add] using htcc)
  have hBv :
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) B 0 1 =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β t 1 := by
    have hshift : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + t) 0 =
        ContinuousLinearMap.id ℝ ℝ := by
      rw [mfderiv_eq_fderiv]
      exact ((hasFDerivAt_id (0 : ℝ)).add_const t).fderiv
    have hβd := (hβ.contMDiffAt htcc).mdifferentiableAt (by simp)
    have hshiftd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun s : ℝ => s + t) 0 := by
      exact ((hasDerivAt_id (0 : ℝ)).add_const t).differentiableAt.mdifferentiableAt
    have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (I'' := 𝓡 n) 0 (by simpa only [zero_add] using hβd) hshiftd
    have hv := congrArg (fun L => L (1 : ℝ)) hcomp
    rw [hshift] at hv
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) B 0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n)) 1 =
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β (0 + t) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n)) 1 at hv
    exact hv.trans (congrArg (fun u : ℝ =>
      (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β u 1))
      (zero_add t))
  obtain ⟨γ, hγ, hγ0, hγ1, hsegment⟩ := hjoin t ht
  obtain ⟨H, hH, hH0, hmajor, hsecond⟩ :=
    exists_squared_distance_upper_support_of_metric_segment g D
      ENNReal.toReal_nonneg hγ hγ0 (by simpa only [B, zero_add] using hγ1)
      hsegment hB (fun u _ => hsec (γ u))
  have hnorm : g.inner (β t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β t 1) = 1 :=
    Real.sqrt_eq_one.mp (hspeed t htcc)
  have hbound : deriv (deriv H) 0 ≤ 2 := by
    have hpair : g.inner (B 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) B 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) B 0 1) = 1 := by
      change g.inner (β (0 + t))
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) B 0 1)
        (show EuclideanSpace ℝ (Fin n) from mfderiv 𝓘(ℝ, ℝ) (𝓡 n) B 0 1) = 1
      rw [zero_add, hBv]
      exact hnorm
    simpa only [hpair, mul_one] using hsecond
  refine ⟨fun s => H (s - t), ?_, ?_, ?_, ?_⟩
  · have hHt : ContDiffAt ℝ 2 H (t - t) := by simpa only [sub_self] using hH
    have hsub : ContDiffAt ℝ 2 (fun s : ℝ => s - t) t :=
      contDiffAt_id.sub contDiffAt_const
    exact ContDiffAt.comp (f := fun s : ℝ => s - t) t hHt hsub
  · simpa only [sub_self] using hH0
  · have hshift : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (0 : ℝ)) := by
      have hc : ContinuousAt (fun s : ℝ => s - t) t :=
        continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hc.tendsto
    filter_upwards [hshift.eventually hmajor] with s hs
    simpa only [B, sub_add_cancel] using hs.2
  · have hfirst : deriv (fun s => H (s - t)) = fun s => deriv H (s - t) :=
      funext fun s => deriv_comp_sub_const H t s
    rw [hfirst, deriv_comp_sub_const, sub_self]
    linarith

theorem corresponding_side_lower_of_cross_segments
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature)
    {γ μ : ℝ → M} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hγ : g.IsGeodesicOn γ (Icc 0 A))
    (hμ : g.IsGeodesicOn μ (Icc 0 B))
    (hγspeed : ∀ t ∈ Icc 0 A,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hμspeed : ∀ t ∈ Icc 0 B,
      g.tangentNorm (μ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) μ t 1) = 1)
    (hbase : γ 0 = μ 0)
    (hγdist : ∀ s ∈ Icc 0 A, g.edist (γ 0) (γ s) = ENNReal.ofReal s)
    (hμdist : ∀ t ∈ Icc 0 B, g.edist (μ 0) (μ t) = ENNReal.ofReal t)
    (hjoin : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, ∃ η : ℝ → M,
      g.IsGeodesicOn η (Icc 0 1) ∧ η 0 = γ s ∧ η 1 = μ t ∧
      ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        g.edist (η u) (η v) = ENNReal.ofReal
          (|u - v| * (g.edist (γ s) (μ t)).toReal)) :
    ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B,
      (g.edist (γ s) (μ t)).toReal ^ 2 ≥ s ^ 2 + t ^ 2 -
        2 * s * t * ((A ^ 2 + B ^ 2 -
          (g.edist (γ A) (μ B)).toReal ^ 2) / (2 * A * B)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcomm (p q : M) : g.edist p q = g.edist q p := Manifold.riemannianEDist_comm
  apply RiemannianMetric.corresponding_side_lower_of_squared_distance_semiconcavity hA hB
  · intro t ht
    have hreverse : ∀ s ∈ Ioo (0 : ℝ) A, ∃ η : ℝ → M,
        g.IsGeodesicOn η (Icc 0 1) ∧ η 0 = μ t ∧ η 1 = γ s ∧
        ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          g.edist (η u) (η v) = ENNReal.ofReal
            (|u - v| * (g.edist (μ t) (γ s)).toReal) := by
      intro s hs
      obtain ⟨η, hη, hη0, hη1, hd⟩ := hjoin s (Ioo_subset_Icc_self hs) t ht
      refine ⟨fun u => η (1 - u), ?_, by simpa using hη1,
        by simpa using hη0, ?_⟩
      · intro u hu
        simpa only [neg_one_mul, neg_add_eq_sub] using
          hη.comp_affine (-1) 1 u ⟨by linarith [hu.2], by linarith [hu.1]⟩
      · intro u hu v hv
        rw [hd _ ⟨by linarith [hu.2], by linarith [hu.1]⟩
          _ ⟨by linarith [hv.2], by linarith [hv.1]⟩, hcomm (μ t) (γ s)]
        congr 2
        rw [show 1 - u - (1 - v) = -(u - v) by ring, abs_neg]
    have hc := squared_distance_sub_sq_concave_of_cross_segments g D hsec
      (μ t) hγ hγspeed hreverse
    simpa only [hcomm (μ t)] using hc
  · intro s hs
    exact squared_distance_sub_sq_concave_of_cross_segments g D hsec
      (γ s) hμ hμspeed (fun t ht => hjoin s hs t (Ioo_subset_Icc_self ht))
  · intro s hs
    rw [← hbase, hcomm (γ s), hγdist s hs, ENNReal.toReal_ofReal hs.1]
  · intro t ht
    rw [hbase, hμdist t ht, ENNReal.toReal_ofReal ht.1]

end PoincareConjecture.M28.Comparison
