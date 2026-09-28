import PoincareConjecture.Proofs.M10.RegularGerms
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

theorem deriv_eq_of_contact {f g : ℝ → ℝ} {s : ℝ}
    (hf : DifferentiableAt ℝ f s) (hg : DifferentiableAt ℝ g s)
    (heq : f s = g s) (hle : ∀ᶠ t in 𝓝 s, f t ≤ g t) :
    deriv f s = deriv g s := by
  have hmin : IsLocalMin (g - f) s := by
    filter_upwards [hle] with t ht
    simpa only [Pi.sub_apply, heq, sub_self] using sub_nonneg.mpr ht
  have hzero := hmin.deriv_eq_zero
  rw [deriv_sub hg hf] at hzero
  exact (sub_eq_zero.mp hzero).symm

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem mvfderiv_eq_zero_of_isLocalMin {f : M → ℝ} {q : M}
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f q) (hmin : IsLocalMin f q) :
    mvfderiv (𝓡 n) f q = 0 := by
  have hmin' : IsLocalMin f ((extChartAt (𝓡 n) q).symm ((extChartAt (𝓡 n) q) q)) := by
    simpa only [extChartAt_to_inv] using hmin
  have hchart := hmin'.comp_continuous (continuousAt_extChartAt_symm (I := 𝓡 n) q)
  rw [hf.mvfderiv]
  ext v
  change (fderivWithin ℝ (writtenInExtChartAt (𝓡 n) (𝓘(ℝ, ℝ)) q f)
    (Set.range (𝓡 n)) ((extChartAt (𝓡 n) q) q)) v = (0 : ℝ)
  simpa only [writtenInExtChartAt, extChartAt_self_eq, modelWithCornersSelf_coe,
    Function.id_comp, Set.range_id, fderivWithin_univ, zero_apply]
    using congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L v)
      hchart.fderiv_eq_zero

theorem mvfderiv_eq_of_contact {f g : M → ℝ} {q : M}
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f q)
    (hg : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) g q)
    (heq : f q = g q) (hle : ∀ᶠ x in 𝓝 q, f x ≤ g x) :
    mvfderiv (𝓡 n) f q = mvfderiv (𝓡 n) g q := by
  have hmin : IsLocalMin (g - f) q := by
    filter_upwards [hle] with x hx
    simpa only [Pi.sub_apply, heq, sub_self] using sub_nonneg.mpr hx
  have hzero := mvfderiv_eq_zero_of_isLocalMin (hg.sub hf) hmin
  rw [mvfderiv_sub hg hf] at hzero
  exact (sub_eq_zero.mp hzero).symm

variable [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p q : M} {τ : ℝ}

theorem barrier_time_deriv_eq (r : ReducedLengthRegularPoint F T τmax p q τ)
    (B : ReducedLengthUpperBarrier F T p q τ) :
    deriv (fun s ↦ B.representative (q, s)) τ =
      deriv (fun s ↦ reducedLength F T p q s) τ := by
  obtain ⟨d, hd⟩ := B.representative_time_derivative
  have hdom : ∀ᶠ z : M × ℝ in 𝓝 (q, τ),
      reducedLength F T p z.1 z.2 ≤ B.representative z :=
    Filter.eventually_of_mem (B.neighborhood_open.mem_nhds B.center_mem) B.dominates
  exact (deriv_eq_of_contact (reducedLength_hasDerivAt r).differentiableAt
    hd.differentiableAt B.touches.symm
    ((continuous_const.prodMk continuous_id).continuousAt hdom)).symm

theorem barrier_spatial_differential_eq
    (r : ReducedLengthRegularPoint F T τmax p q τ)
    (B : ReducedLengthUpperBarrier F T p q τ) :
    mvfderiv (𝓡 n) (fun x ↦ B.representative (x, τ)) q =
      mvfderiv (𝓡 n) (fun x ↦ reducedLength F T p x τ) q := by
  have hdom : ∀ᶠ z : M × ℝ in 𝓝 (q, τ),
      reducedLength F T p z.1 z.2 ≤ B.representative z :=
    Filter.eventually_of_mem (B.neighborhood_open.mem_nhds B.center_mem) B.dominates
  exact (mvfderiv_eq_of_contact
    ((reducedLength_space_contMDiffAt r).mdifferentiableAt (by simp))
    (B.representative_space_smooth.mdifferentiableAt (by simp)) B.touches.symm
    ((continuous_id.prodMk continuous_const).continuousAt hdom)).symm

theorem barrier_gradientNormSq_eq (r : ReducedLengthRegularPoint F T τmax p q τ)
    (B : ReducedLengthUpperBarrier F T p q τ) :
    reducedLengthGradientNormSq F T B.representative τ q =
      reducedLengthGradientNormSq F T (fun z ↦ reducedLength F T p z.1 z.2) τ q := by
  unfold reducedLengthGradientNormSq
  rw [barrier_spatial_differential_eq r B]

theorem reducedLength_local_derivative_bounds [ConnectedSpace M]
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p)
    (z : M × ℝ) (hz : z ∈ Set.univ ×ˢ Set.Ioo 0 τmax) :
    ∃ U : Set (M × ℝ), IsOpen U ∧ z ∈ U ∧
      U ⊆ Set.univ ×ˢ Set.Ioo 0 τmax ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ U ∩ G.regularImage,
        |deriv (fun s ↦ reducedLength F T p w.1 s) w.2| ≤ C ∧
        reducedLengthGradientNormSq F T
          (fun y ↦ reducedLength F T p y.1 y.2) w.2 w.1 ≤ C := by
  obtain ⟨N, hNopen, hzN, hNtime, C, hC, hbounds⟩ :=
    hDifferential.local_upper_barrier_bounds p z hz
  refine ⟨N, hNopen, hzN, hNtime, C, hC, ?_⟩
  intro w hw
  obtain ⟨B, htime, hspace, _⟩ := hbounds w hw.1
  let r := G.regular_point w hw.2
  rw [barrier_time_deriv_eq r B] at htime
  rw [barrier_gradientNormSq_eq r B] at hspace
  exact ⟨htime, hspace⟩

end PoincareConjecture.M10
