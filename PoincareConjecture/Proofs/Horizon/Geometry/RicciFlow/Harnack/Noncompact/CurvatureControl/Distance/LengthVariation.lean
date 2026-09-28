import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Curve.Velocity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private lemma contMDiffAt_speed_sq
    (F : RicciFlow n M J) {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {s u : ℝ} (hs : s ∈ interior J) (hu : u ∈ I) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × ℝ => (F.metric p.1).inner (γ p.2)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ p.2 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ p.2 1)) (s, u) := by
  have hg := (F.smooth (s, γ u) ⟨interior_subset hs, mem_univ _⟩).contMDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp hs) univ_mem)
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun p : ℝ × ℝ => (p.1, γ p.2)) (s, u) :=
    contMDiffAt_fst.prodMk
    ((hγ u hu).contMDiffAt (hI.mem_nhds hu) |>.comp (s, u) contMDiffAt_snd)
  have hv : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod (𝓡 n)) ∞
      (fun p : ℝ × ℝ => (⟨γ p.2, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ p.2 1⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)))) (s, u) :=
    ((Poincare.Manifold.contMDiffOn_velocity_lift hI hγ u hu).contMDiffAt
      (hI.mem_nhds hu)).comp (s, u) contMDiffAt_snd
  have h := (hg.comp (s, u) hbase).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hv hv
  exact (contMDiffAt_totalSpace.mp h).2

theorem continuousAt_curve_speed
    (F : RicciFlow n M J) {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {s u : ℝ} (hs : s ∈ interior J) (hu : u ∈ I) :
    ContinuousAt (fun p : ℝ × ℝ => (F.metric p.1).tangentNorm (γ p.2)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ p.2 1)) (s, u) :=
  Real.continuous_sqrt.continuousAt.comp
    (contMDiffAt_speed_sq F hI hγ hs hu).continuousAt

theorem hasDerivAt_integral_speed
    (F : RicciFlow n M J) {γ : ℝ → M} {I : Set ℝ} {a b t : ℝ}
    (hab : a ≤ b) (hI : IsOpen I) (hsub : Icc a b ⊆ I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (ht : t ∈ interior J)
    (hvel : ∀ u ∈ Icc a b, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1 ≠ 0) :
    HasDerivAt (fun s => ∫ u in a..b,
      (F.metric s).tangentNorm (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1))
      (∫ u in a..b, -(F.connection t).ricci (γ u)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) /
        (F.metric t).tangentNorm (γ u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1)) t := by
  let v := fun u => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1
  let G := fun s u => (F.metric s).inner (γ u) (v u) (v u)
  let speed := fun s u => Real.sqrt (G s u)
  let speed' := fun s u => deriv (fun r => G r u) s / (2 * Real.sqrt (G s u))
  obtain ⟨α, β, htcc, htnhds, hwin⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (isOpen_interior.mem_nhds ht)
  have htopen : t ∈ Ioo α β := by
    simpa only [interior_Icc] using mem_interior_iff_mem_nhds.mpr htnhds
  let K : Set (ℝ × ℝ) := Icc α β ×ˢ Icc a b
  have hG : ∀ p ∈ K, ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × ℝ => G q.1 q.2) p := by
    intro p hp
    exact contMDiffAt_speed_sq F hI hγ (hwin hp.1) (hsub hp.2)
  have hpos : ∀ s, ∀ u ∈ Icc a b, 0 < G s u := by
    intro s u hu
    exact (F.metric s).pos (γ u) (v u) (hvel u hu)
  have hspeed : ContinuousOn (fun p : ℝ × ℝ => speed p.1 p.2) K :=
    fun p hp => Real.continuous_sqrt.continuousAt.comp_continuousWithinAt
      (hG p hp).continuousAt.continuousWithinAt
  have hspeed' : ContinuousOn (fun p : ℝ × ℝ => speed' p.1 p.2) K := by
    intro p hp
    exact ((Poincare.Manifold.contMDiffAt_deriv_time (hG p hp)).continuousAt.div
      (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        (hG p hp).continuousAt))
      (ne_of_gt (mul_pos two_pos (Real.sqrt_pos.mpr (hpos p.1 p.2 hp.2))))).continuousWithinAt
  have hslice : ∀ s ∈ Icc α β, ContinuousOn (speed s) (Icc a b) := by
    intro s hs
    have hparam : ContinuousOn (fun u : ℝ => (s, u)) (Icc a b) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hc := hspeed.comp hparam (fun u hu => show (s, u) ∈ K from ⟨hs, hu⟩)
    exact hc
  have hslice' : ∀ s ∈ Icc α β, ContinuousOn (speed' s) (Icc a b) := by
    intro s hs
    have hparam : ContinuousOn (fun u : ℝ => (s, u)) (Icc a b) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hc := hspeed'.comp hparam (fun u hu => show (s, u) ∈ K from ⟨hs, hu⟩)
    exact hc
  have hpoint : ∀ s ∈ Ioo α β, ∀ u ∈ Icc a b,
      HasDerivAt (fun r => speed r u) (speed' s u) s := by
    intro s hs u hu
    have hmetric := (F.equation s (interior_subset (hwin ⟨hs.1.le, hs.2.le⟩))
      (γ u) (v u) (v u)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp (hwin ⟨hs.1.le, hs.2.le⟩))
    exact hmetric.differentiableAt.hasDerivAt.sqrt (ne_of_gt (hpos s u hu))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hspeed'
  have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (F := speed) (F' := speed') (x₀ := t)
    (bound := fun _ => C) (s := Ioo α β) (Ioo_mem_nhds htopen.1 htopen.2)
    (eventually_of_mem (Ioo_mem_nhds htopen.1 htopen.2) (fun s hs => by
      rw [uIoc_of_le hab]
      exact ((hslice s ⟨hs.1.le, hs.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc))
    ((hslice t htcc).intervalIntegrable_of_Icc hab)
    (by
      rw [uIoc_of_le hab]
      exact ((hslice' t htcc).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc)
    (Eventually.of_forall (fun u hu s hs => by
      rw [uIoc_of_le hab] at hu
      exact hC (s, u) ⟨⟨hs.1.le, hs.2.le⟩, ⟨hu.1.le, hu.2⟩⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun u hu s hs => by
      rw [uIoc_of_le hab] at hu
      exact hpoint s hs u ⟨hu.1.le, hu.2⟩))
  apply hkey.2.congr_deriv
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  dsimp only [speed', G, v]
  rw [(F.equation t (interior_subset ht) (γ u)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht) |>.deriv]
  dsimp only [RiemannianMetric.tangentNorm]
  ring

end PoincareConjecture.RicciFlow
