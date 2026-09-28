import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.DeckMotion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem contDiffAt_of_continuousAt_lift
    {f h : EuclideanSpace ℝ (Fin n) → M}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ y ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f y))
    (hdx : d x ∈ U) (hd : ContinuousAt d x)
    (hh : ContMDiffAt (𝓡 n) (𝓡 n) ∞ h x)
    (hproj : (f ∘ d) =ᶠ[𝓝 x] h) : ContDiffAt ℝ ∞ d x := by
  obtain ⟨e, hde, _, heq, _, hes⟩ := exists_smooth_inverse_branch hU hf hbij hdx
  have hhx : h x ∈ e.target := by
    rw [← hproj.self_of_nhds]
    change f (d x) ∈ e.target
    rw [← heq hde]
    exact e.map_source hde
  have hs : ContDiffAt ℝ ∞ (e.symm ∘ h) x := contMDiffAt_iff_contDiffAt.mp
    ((hes.contMDiffAt (e.open_target.mem_nhds hhx)).comp x hh)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hd.preimage_mem_nhds (e.open_source.mem_nhds hde), hproj] with y hy hpy
  change d y = e.symm (h y)
  rw [← hpy]
  change d y = e.symm (f (d y))
  rw [← heq hy, e.left_inv hy]

theorem exists_smooth_radial_deck_motion [T2Space M]
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (hspeed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (f (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => f (u • v)) t 1) ≤ ‖v‖)
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) (hx : f x = f 0) :
    let U := {v : EuclideanSpace ℝ (Fin n) | ‖(x : EuclideanSpace ℝ (Fin n))‖ + 2 * ‖v‖ < R}
    ∃ d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ d U ∧ MapsTo d U (Metric.ball 0 R) ∧
      EqOn (f ∘ d) f U ∧ d 0 = x ∧
      (∀ v ∈ U, ‖d v - x‖ ≤ 2 * ‖v‖) ∧
      ((x : EuclideanSpace ℝ (Fin n)) ≠ 0 → ∀ v ∈ U, d v ≠ v) := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin n)
  let U := {v : E | ‖(x : E)‖ + 2 * ‖v‖ < R}
  obtain ⟨D, hDproj, hDbound, _, hD0, hDne⟩ :=
    exists_radial_deck_motion g hf hbij hlower hspeed x hx
  let d : E → E := fun v => if hv : v ∈ U then D ⟨v, hv⟩ else x
  have hd (v : E) (hv : v ∈ U) : d v = D ⟨v, hv⟩ := dif_pos hv
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hcont : ContinuousOn d U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hD : Continuous (fun v : U => (D v : E)) :=
      continuous_subtype_val.comp D.continuous
    exact hD.congr fun v => (hd v v.property).symm
  have hproj : EqOn (f ∘ d) f U := by
    intro v hv
    change f (d v) = f v
    rw [hd v hv]
    exact hDproj ⟨v, hv⟩
  have hmem : MapsTo d U (Metric.ball 0 R) := by
    intro v hv
    rw [hd v hv]
    exact (D ⟨v, hv⟩).property
  have hzero : (0 : E) ∈ U := by
    simpa only [U, mem_ofPred_eq, norm_zero, mul_zero, add_zero, Metric.mem_ball,
      dist_zero_right] using x.property
  refine ⟨d, ?_, hmem, hproj, ?_, ?_, ?_⟩
  · intro v hv
    have hvR : v ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right]
      have hv' : ‖(x : E)‖ + 2 * ‖v‖ < R := hv
      linarith [norm_nonneg (x : E), norm_nonneg v]
    exact (contDiffAt_of_continuousAt_lift Metric.isOpen_ball hf hbij (hmem hv)
      (hcont.continuousAt (hU.mem_nhds hv))
      (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hvR))
      (hproj.eventuallyEq_of_mem (hU.mem_nhds hv))).contDiffWithinAt
  · rw [hd 0 hzero]
    exact congrArg Subtype.val (hD0 ⟨0, hzero⟩ rfl)
  · intro v hv
    rw [hd v hv]
    exact hDbound ⟨v, hv⟩
  · intro hxne v hv
    rw [hd v hv]
    exact hDne hxne ⟨v, hv⟩

theorem pullbackCoefficients_deck_motion
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (d x))
    (hd : DifferentiableAt ℝ d x)
    (hproj : (f ∘ d) =ᶠ[𝓝 x] f)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients f (d x) (fderiv ℝ d x v) (fderiv ℝ d x w) =
      g.pullbackCoefficients f x v w := by
  have hchain := mfderiv_comp x hf hd.mdifferentiableAt
  rw [hproj.mfderiv_eq, mfderiv_eq_fderiv] at hchain
  have hv := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) => A v) hchain
  have hw := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) => A w) hchain
  simp only [ContinuousLinearMap.comp_apply, TangentSpace] at hv hw
  change g.inner (f (d x))
    (mfderiv (𝓡 n) (𝓡 n) f (d x) (fderiv ℝ d x v))
    (mfderiv (𝓡 n) (𝓡 n) f (d x) (fderiv ℝ d x w)) =
      g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
  simp only [TangentSpace]
  rw [← hv, ← hw]
  exact congrArg (fun p : M => g.inner p
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) f x v)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) f x w)) hproj.self_of_nhds

end PoincareConjecture
