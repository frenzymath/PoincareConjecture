import PoincareConjecture.Proofs.M35.CapGeometry.RadialFieldSystem
import PoincareConjecture.Proofs.M35.Thm12_28.PointIsometryJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

noncomputable section

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ
local notation "GammaB" => V →L[ℝ] V →L[ℝ] V
local notation "RadialC" => B × (GammaB × B)

local instance retainedRadialMetricNormedGroup : NormedAddCommGroup B := inferInstance
local instance retainedRadialMetricNormedSpace : NormedSpace ℝ B := inferInstance
local instance retainedRadialGammaNormedGroup : NormedAddCommGroup GammaB := inferInstance
local instance retainedRadialGammaNormedSpace : NormedSpace ℝ GammaB := inferInstance
local instance retainedRadialCoefficientNormedGroup : NormedAddCommGroup RadialC := inferInstance
local instance retainedRadialCoefficientNormedSpace : NormedSpace ℝ RadialC := inferInstance



theorem radial_pullback_norm_le
    {g G : RiemannianMetric 3 V}
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V,
        G.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = G.inner x u v)
    {f : V → V} {x : V} (hinv : (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible)
    (hmetric : ∀ u v : V, g.inner x u v = G.inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v))
    (hzero : f x ≠ 0) {a : ℝ} (ha : 0 < a)
    (hell : ∀ v : V, a * ‖v‖ ^ 2 ≤ g.inner x v v) :
    ‖pullback ℝ f (radialUnitField G) x‖ ≤ a⁻¹ + 1 := by
  let Y := mpullback (𝓡 3) (𝓡 3) f (radialUnitField G)
  have hu : g.inner x (Y x) (Y x) = 1 := by
    rw [hmetric]
    simp only [Y, mpullback, hinv.self_apply_inverse]
    exact radialUnitField_unit G hrotation hzero
  have huE : g.inner x (pullback ℝ f (radialUnitField G) x)
      (pullback ℝ f (radialUnitField G) x) = 1 := by
    simpa only [Y, mpullback_eq_pullback] using! hu
  have h := hell (pullback ℝ f (radialUnitField G) x)
  have hle : a * ‖pullback ℝ f (radialUnitField G) x‖ ^ 2 ≤ 1 :=
    h.trans huE.le
  have hs : ‖pullback ℝ f (radialUnitField G) x‖ ^ 2 ≤ 1 / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using hle
  simp only [one_div] at hs
  nlinarith only [hs, inv_pos.mpr ha,
    sq_nonneg (‖pullback ℝ f (radialUnitField G) x‖ - 1 / 2)]




theorem retained_radial_field_shape_jets
    {gseq Gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (DGseq : ∀ k, LeviCivitaData (Gseq k))
    (D : LeviCivitaData g) (f : ℕ → V → V) (pseq : ℕ → V) (p : V) (n : ℕ)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V,
        (Gseq k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (Gseq k).inner x u v)
    (hf : ∀ k, ∀ᶠ y in 𝓝 (pseq k), ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f k) y)
    (hinv : ∀ k, ∀ᶠ y in 𝓝 (pseq k), (mfderiv (𝓡 3) (𝓡 3) (f k) y).IsInvertible)
    (hmetric : ∀ k, ∀ᶠ y in 𝓝 (pseq k), ∀ u v : V,
      (gseq k).inner y u v = (Gseq k).inner (f k y)
        (mfderiv (𝓡 3) (𝓡 3) (f k) y u) (mfderiv (𝓡 3) (𝓡 3) (f k) y v))
    (hzero : ∀ k, f k (pseq k) ≠ 0)
    {a : ℝ} (ha : 0 < a)
    (hell : ∀ k (v : V), a * ‖v‖ ^ 2 ≤ (gseq k).inner (pseq k) v v)
    (hshape : ∃ C : ℝ, ∀ k,
      |axisWarpingSlope (Gseq k) ‖f k (pseq k)‖ /
        axisWarpingRadius (Gseq k) ‖f k (pseq k)‖| ≤ C)
    (hjet : ∀ m ≤ n + 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    HasUniformJetBoundsAt (n + 1)
      (fun k y => (pullback ℝ (f k) (radialUnitField (Gseq k)) y,
        axisWarpingSlope (Gseq k) ‖f k y‖ / axisWarpingRadius (Gseq k) ‖f k y‖)) pseq := by
  let Z k := pullback ℝ (f k) (radialUnitField (Gseq k))
  let s k y := axisWarpingSlope (Gseq k) ‖f k y‖ / axisWarpingRadius (Gseq k) ‖f k y‖
  have hfs k := contMDiffAt_iff_contDiffAt.mp (hf k).self_of_nhds
  have hi k : (fderiv ℝ (f k) (pseq k)).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using (hinv k).self_of_nhds
  have hZ k : ContDiffAt ℝ ∞ (Z k) (pseq k) :=
    euclidean_radial_pullback_contDiffAt (Gseq k) (hfs k) (hi k) (hzero k)
  have hs k : ContDiffAt ℝ ∞ (s k) (pseq k) :=
    (radial_shape_contDiffAt (Gseq k) (hzero k)).comp (pseq k) (hfs k)
  have hB k := (gseq k).contDiffAt_euclideanCoefficients (pseq k)
  have hBj : HasUniformJetBoundsAt (n + 1)
      (fun k => (gseq k).euclideanCoefficients) pseq := by
    intro m hm
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hjet m (by omega))).exists_norm_le
    exact ⟨C, fun k => hC _ (mem_range_self k)⟩
  have hGamma := finite_christoffel_jets_at hB hBj ha hell
  have hsGamma k : ContDiffAt ℝ ∞
      (CoordinateExponential.christoffelBilinear (gseq k).euclideanCoefficients) (pseq k) :=
    CoordinateExponential.contDiffAt_christoffelBilinear (hB k)
      (CoordinateTransition.isInvertible_of_uniformEllipticity ha (hell k))
  have hRicci : HasUniformJetBoundsAt n
      (fun k => radialRicciCoefficients (Dseq k)) pseq := by
    intro m hm
    have h := radialRicciCoefficients_jets_tendsto Dseq D pseq p m
      (fun r hr => hjet r (by omega))
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_norm_le
    exact ⟨C, fun k => hC _ (mem_range_self k)⟩
  have hsRicci k := radialRicciCoefficients_contDiffAt (Dseq k) (pseq k)
  have hC := (hBj.mono_order (Nat.le_succ n)).prodMk
    (hGamma.prodMk hRicci hsGamma hsRicci) hB
    (fun k => (hsGamma k).prodMk (hsRicci k))
  obtain ⟨C, hCshape⟩ := hshape
  refine radial_field_shape_jets_at
    (fun k => (hB k).prodMk ((hsGamma k).prodMk (hsRicci k)))
    (fun k => (hZ k).prodMk (hs k)) hC
    ⟨max (a⁻¹ + 1) C, fun k => ?_⟩ ?_
  · rw [Prod.norm_def]
    exact max_le_max (radial_pullback_norm_le (hrotation k) (hinv k).self_of_nhds
      (hmetric k).self_of_nhds (hzero k) ha (hell k)) (hCshape k)
  · intro k
    have hn : ∀ᶠ y in 𝓝 (pseq k), f k y ≠ 0 :=
      (hfs k).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (hzero k))
    filter_upwards [hf k, (hinv k).eventually_nhds, (hmetric k).eventually_nhds, hn]
      with y hfy hiy hmy hny
    exact (radial_field_shape_hasFDerivAt (Dseq k) (DGseq k) (hrotation k)
      hfy hiy hmy hny).fderiv

end

end PoincareConjecture.M35
