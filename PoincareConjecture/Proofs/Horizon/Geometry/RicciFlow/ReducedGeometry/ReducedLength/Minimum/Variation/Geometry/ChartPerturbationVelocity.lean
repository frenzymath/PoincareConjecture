import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.WeightedChartPerturbation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.VelocityChainRules
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.CompactFieldExtension







set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u v

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem weightedChartPerturbation_curveVelocity
    (p : M) (W : Set ℝ) (ρ : ℝ → ℝ) (B : ℝ → P →L[ℝ] E)
    (f : ℝ × P → M) (s : ℝ) (z : P)
    (hf : MDifferentiableAt (𝓘(ℝ, ℝ × P)) (𝓡 n) f (s, 0))
    (hchart : ρ s ≠ 0 → s ∈ W ∧ f (s, 0) ∈ (chartAt E p).source) :
    (curveVelocity (n := n)
        (fun u : ℝ ↦ weightedChartPerturbation p W ρ B f (s, u • z)) 0 : E) =
      @HAdd.hAdd E E E _
        (curveVelocity (n := n) (fun u : ℝ ↦ f (s, u • z)) 0)
        (chartVectorField p (ρ s • B s z) (f (s, 0))) := by
  classical
  by_cases hzero : ρ s = 0
  · have heq : (fun u : ℝ ↦ weightedChartPerturbation p W ρ B f (s, u • z)) =
        (fun u : ℝ ↦ f (s, u • z)) := by
      funext u
      exact weightedChartPerturbation_eq_of_zero p W ρ B f (s, u • z) (Or.inl hzero)
    rw [heq, hzero]
    simp only [chartVectorField, VectorField.mpullback, zero_smul, map_zero, add_zero]
  · let e := chartAt E p
    let β : ℝ → M := fun u ↦ f (s, u • z)
    have hβ0 : β 0 = f (s, 0) := by simp only [β, zero_smul]
    have hparam : ContDiff ℝ ∞ (fun u : ℝ ↦ (s, u • z)) :=
      contDiff_const.prodMk (contDiff_id.smul contDiff_const)
    have hf' : MDifferentiableAt (𝓘(ℝ, ℝ × P)) (𝓡 n) f (s, (0 : ℝ) • z) := by
      simpa only [zero_smul] using hf
    have hβ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) β 0 :=
      hf'.comp 0 (hparam.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    have hsrc : β 0 ∈ e.source := hβ0.symm ▸ (hchart hzero).2
    let a : E := ρ s • B s z
    let v : E := mfderiv (𝓡 n) (𝓡 n) e (β 0) (curveVelocity β 0)
    let k : ℝ → E := fun u ↦ e (β u) + u • a
    have hk0 : k 0 = e (β 0) := by simp only [k, zero_smul, add_zero]
    have hk : HasDerivAt k (v + a) 0 := by
      exact (hasDerivAt_chart_curve p β 0 hsrc hβ).add
        (by simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const a)
    have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), β u ∈ e.source :=
      hβ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hsrc)
    have heq : (fun u : ℝ ↦ weightedChartPerturbation p W ρ B f (s, u • z)) =ᶠ[𝓝 0]
        (fun u ↦ e.symm (k u)) := by
      filter_upwards [hnear] with u hu
      change (if s ∈ W ∧ β u ∈ e.source then
        e.symm (e (β u) + ρ s • B s (u • z)) else β u) = e.symm (k u)
      rw [if_pos ⟨(hchart hzero).1, hu⟩, map_smul, smul_comm (ρ s) u]
    have htarget : k 0 ∈ e.target := hk0.symm ▸ e.map_source hsrc
    have hvel : (curveVelocity (n := n) (fun u ↦ e.symm (k u)) 0 : E) =
        mfderiv (𝓡 n) (𝓡 n) e.symm (k 0) (v + a) := by
      simpa only [curveVelocityWithin, curveVelocity, mfderivWithin_univ] using
        curveVelocityWithin_inverseChart p k Set.univ 0 _ uniqueDiffWithinAt_univ hk htarget
    rw [curveVelocity_congr_of_eventuallyEq heq, hvel, hk0]
    have hinverse := chartVectorField_at_inverse p (v + a)
      (e (β 0)) (e.map_source hsrc)
    rw [e.left_inv hsrc] at hinverse
    calc
      _ = chartVectorField p (v + a) (β 0) := hinverse.symm
      _ = _ := by
        have hrecover := chartVectorField_differential p (β 0) (curveVelocity β 0) hsrc
        have hadd := (mfderiv (𝓡 n) (𝓡 n) e (β 0)).inverse.map_add v a
        change chartVectorField p (v + a) (β 0) =
          chartVectorField p v (β 0) + chartVectorField p a (β 0) at hadd
        change chartVectorField p v (β 0) = curveVelocity β 0 at hrecover
        rw [hrecover] at hadd
        have hpoint : (chartVectorField p a (β 0) : E) =
            chartVectorField p a (f (s, 0)) :=
          congrArg (fun x ↦ (chartVectorField p a x : E)) hβ0
        exact hadd.trans (congrArg (fun w : E ↦ @HAdd.hAdd E E E _
          (curveVelocity β 0) w) hpoint)

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
