import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chartCoefficients_self (g : RiemannianMetric n M) (p : M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p) v w =
      g.inner p v w := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := p)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  change g.inner ((extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p) v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p) w) = _
  have hvec (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p) a = a :=
    congrArg (fun L => L a) h
  rw [hvec v, hvec w]
  exact congrArg (fun y => g.inner y v w)
    ((extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p))

theorem exists_tangentBall_subset_nhds (g : RiemannianMetric n M) (p : M)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : V ∈ 𝓝 0) :
    ∃ r : ℝ, 0 < r ∧ {v | g.tangentNorm p v < r} ⊆ V := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (NormedAddCommGroup E)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound
    (B := fun _ : E => (g.inner p : E →L[ℝ] E →L[ℝ] ℝ))
    (K := {(0 : E)}) isCompact_singleton continuousOn_const
    (fun _ _ v hv => g.pos p v hv)
  refine ⟨Real.sqrt c * ε, mul_pos (Real.sqrt_pos.mpr hc) hε, ?_⟩
  intro v hv
  apply hεV
  rw [Metric.mem_ball, dist_zero_right]
  have hlow : Real.sqrt c * ‖(v : E)‖ ≤ g.tangentNorm p v := by
    have h := Real.sqrt_le_sqrt (hbound 0 (mem_singleton 0) v)
    simpa only [tangentNorm, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg (v : E))] using! h
  have hsmall := lt_of_le_of_lt hlow hv
  exact (mul_lt_mul_iff_right₀ (Real.sqrt_pos.mpr hc)).mp hsmall

theorem exists_exponential_chart_gauss (g : RiemannianMetric n M) (p : M) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ e : OpenPartialHomeomorph E M,
      (0 : E) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      (∀ v ∈ e.source, ∀ w : E,
        g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
          (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w) ∧
      (∃ r : ℝ, 0 < r ∧ {v : E | g.tangentNorm p v < r} ⊆ e.source) ∧
      ∃ Γ : E × ℝ → E × E,
        ContDiffOn ℝ ∞ Γ (e.source ×ˢ Ioo (-2 : ℝ) 2) ∧
        ∀ v ∈ e.source,
          Γ (v, 0) = (c p, v) ∧ c.symm (Γ (v, 1)).1 = e v ∧
          ∀ t ∈ Ioo (-2 : ℝ) 2,
            (Γ (v, t)).1 ∈ c.target ∧
            HasDerivAt (fun s => Γ (v, s)) (coordinateGeodesicField B (Γ (v, t))) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  have hU : IsOpen c.target := isOpen_extChartAt_target (I := 𝓡 n) p
  have hB : ContDiffOn ℝ ∞ B c.target := g.contDiffOn_chartCoefficients p
  have hinv : ∀ y ∈ c.target, (B y).IsInvertible :=
    fun y hy => g.isInvertible_chartCoefficients p hy
  have hsymm : ∀ y ∈ c.target, ∀ u v, B y u v = B y v u :=
    fun y _ u v => g.symm _ _ _
  obtain ⟨D⟩ := CoordinateExponential.exists_localFlowData hU hB hinv hsymm
    (mem_extChartAt_target p)
  obtain ⟨f, hzero, hsourceD, hfD, hf, hfinv⟩ := D.exists_openPartialHomeomorph
  have hfzero : f 0 = c p := by rw [hfD]; exact D.exponential_zero
  have htarget : f.target ⊆ c.target := by
    intro y hy
    have h := D.trajectory_mem (hsourceD (f.map_target hy))
      (by norm_num : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2)
    rwa [D.trajectory_endpoint, ← hfD, f.right_inv hy] at h
  let e : OpenPartialHomeomorph E M := f.trans (chartAt E p).symm
  have hsource : e.source = f.source := by
    ext v
    constructor
    · exact fun hv => hv.1
    · intro hv
      refine ⟨hv, ?_⟩
      simpa [c, extChartAt_target] using htarget (f.map_source hv)
  have heapply : ∀ v, e v = c.symm (f v) := fun _ => rfl
  have hesmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (c.symm ∘ f) e.source
    rw [hsource]
    exact (contMDiffOn_extChartAt_symm p).comp
      (contMDiffOn_iff_contDiffOn.mpr hf) (fun v hv => htarget (f.map_source hv))
  have heinverse : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f.symm ∘ c) e.target
    apply (contMDiffOn_iff_contDiffOn.mpr hfinv).comp
      ((contMDiffOn_extChartAt (I := 𝓡 n) (x := p)).mono (fun y hy => hy.1))
    exact fun y hy => hy.2
  refine ⟨e, hsource.symm ▸ hzero, ?_, hesmooth, heinverse, ?_,
    g.exists_tangentBall_subset_nhds p (e.open_source.mem_nhds (hsource.symm ▸ hzero)),
    (fun z => D.trajectory z.1 z.2), ?_, ?_⟩
  · rw [heapply, hfzero]
    exact c.left_inv (mem_extChartAt_source p)
  · intro v hv w
    have hvf : v ∈ f.source := hsource ▸ hv
    have hc := ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
      (hU.mem_nhds (htarget (f.map_source hvf)))).mdifferentiableAt (by simp)
    have hfm : MDifferentiableAt (𝓡 n) (𝓡 n) f v :=
      mdifferentiableAt_iff_differentiableAt.mpr
        ((hf.contDiffAt (f.open_source.mem_nhds hvf)).differentiableAt (by simp))
    have hchain := mfderiv_comp v hc hfm
    rw [mfderiv_eq_fderiv] at hchain
    change mfderiv (𝓡 n) (𝓡 n) e v =
      (mfderiv (𝓡 n) (𝓡 n) c.symm (f v)).comp (fderiv ℝ (f : E → E) v) at hchain
    rw [hchain]
    change B (f v) (fderiv ℝ (f : E → E) v v) (fderiv ℝ (f : E → E) v w) = _
    rw [hfD, D.gauss_identity hU hB hinv hsymm (hsourceD hvf) w]
    exact g.chartCoefficients_self p v w
  · exact D.smooth_trajectory.mono
      (Set.prod_mono (fun v hv => hsourceD (hsource ▸ hv)) Subset.rfl)
  · intro v hv
    have hvD := hsourceD (hsource ▸ hv)
    refine ⟨D.trajectory_initial hvD, ?_, fun t ht =>
      ⟨D.trajectory_mem hvD ht, D.trajectory_hasDerivAt hvD ht⟩⟩
    rw [D.trajectory_endpoint, heapply, hfD]

end PoincareConjecture.RiemannianMetric
