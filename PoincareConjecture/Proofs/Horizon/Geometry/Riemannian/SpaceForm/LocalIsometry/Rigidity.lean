import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.ExponentialMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Transitions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

omit [IsManifold (𝓡 n) ∞ M] in
private theorem coordDeriv_comp_eq_of_firstOrder
    {f k : M → N} {p : M} {γ : ℝ → M} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ 0)
    (hγ0 : γ 0 = p) (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f p)
    (hk : MDifferentiableAt (𝓡 n) (𝓡 n) k p) (hpos : f p = k p)
    (hder : mfderiv (𝓡 n) (𝓡 n) f p = mfderiv (𝓡 n) (𝓡 n) k p) :
    deriv (fun t => extChartAt (𝓡 n) (f p) (f (γ t))) 0 =
      deriv (fun t => extChartAt (𝓡 n) (f p) (k (γ t))) 0 := by
  subst p
  let c := extChartAt (𝓡 n) (f (γ 0))
  have hcf : MDifferentiableAt (𝓡 n) (𝓡 n) c (f (γ 0)) :=
    mdifferentiableAt_extChartAt (mem_chart_source _ _)
  have hck : MDifferentiableAt (𝓡 n) (𝓡 n) c (k (γ 0)) := hpos ▸ hcf
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (c ∘ f ∘ γ) 0 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (c ∘ k ∘ γ) 0 := by
    rw [mfderiv_comp 0 hcf (hf.comp 0 hγ), mfderiv_comp 0 hck (hk.comp 0 hγ),
      mfderiv_comp 0 hf hγ, mfderiv_comp 0 hk hγ, hder]
    simp only [Function.comp_apply]
    erw [hpos]
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at hd
  exact congrArg (fun L => L 1) hd

theorem local_isometry_germ_ext [T2Space M] [CompactSpace M] [T2Space N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f k : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ k U)
    (hfmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (hkmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (k x)
        (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w))
    {p : M} (hp : p ∈ U) (hpos : f p = k p)
    (hder : mfderiv (𝓡 n) (𝓡 n) f p = mfderiv (𝓡 n) (𝓡 n) k p) :
    f =ᶠ[𝓝 p] k := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p (R := 1)
      (by norm_num) isClosed_closure.isCompact
  have heAt := he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simp : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 1))
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p heAt he0 hed hL
  have hbij : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e 0) :=
    (RiemannianMetric.euclideanMetric n).mfderiv_bijective_of_pullback_eq g 0 hnorm
  have hmap : map e (𝓝 0) = 𝓝 p := by
    rw [Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective heAt hbij, he0]
  have hnear : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ e ⁻¹' U ∈ 𝓝 0 :=
    inter_mem (Metric.isOpen_ball.mem_nhds (by simp))
      (heAt.continuousAt.preimage_mem_nhds (he0.symm ▸ hU.mem_nhds hp))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  rw [← hmap]
  change ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), f (e v) = k (e v)
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with v hv
  have hv1 := (hrsub hv).1
  let γ : ℝ → M := fun t => e (t • v)
  have hdomain (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hv)
  have hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1) :=
    fun t ht => (hgeo v hv1).1 t (hrsub (hdomain t ht)).1
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) U := fun t ht => (hrsub (hdomain t ht)).2
  have hγ0 : γ 0 = p := by simpa [γ] using he0
  have hfg := hγ.comp_local_isometry_manifold hU hf hfmetric hγU
  have hkg := hγ.comp_local_isometry_manifold hU hk hkmetric hγU
  have hvel := coordDeriv_comp_eq_of_firstOrder
    ((hγ.contMDiffAt (by simp : (0 : ℝ) ∈ Icc 0 1)).mdifferentiableAt (by simp))
    hγ0 ((hf.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
    ((hk.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)) hpos hder
  have heq := hfg.eq_nhds_on_of_initial_data hkg (convex_Icc _ _).isPreconnected
    (t₀ := 0) (by simp) (f p)
    (by simpa only [Function.comp_apply, hγ0] using mem_extChartAt_source (f p))
    (by simpa only [Function.comp_apply, hγ0] using hpos) hvel
  simpa only [Function.comp_apply, γ, one_smul] using (heq 1 (by simp)).self_of_nhds

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] in
private theorem mfderiv_eq_of_frequently_equal_germs
    {f k : M → N} {p : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f p)
    (hk : ContMDiffAt (𝓡 n) (𝓡 n) ∞ k p) (hpos : f p = k p)
    (hfreq : ∃ᶠ x in 𝓝 p, f =ᶠ[𝓝 x] k) :
    mfderiv (𝓡 n) (𝓡 n) f p = mfderiv (𝓡 n) (𝓡 n) k p := by
  let c := extChartAt (𝓡 n) p
  let d := extChartAt (𝓡 n) (f p)
  let F := d ∘ f ∘ c.symm
  let K := d ∘ k ∘ c.symm
  have hF : ContDiffAt ℝ ∞ F (c p) := by
    simpa [F, c, d, writtenInExtChartAt, contDiffWithinAt_univ]
      using (contMDiffAt_iff.mp hf).2
  have hK : ContDiffAt ℝ ∞ K (c p) := by
    simpa [K, c, d, hpos, writtenInExtChartAt, contDiffWithinAt_univ]
      using (contMDiffAt_iff.mp hk).2
  have hcmap : map c.symm (𝓝 (c p)) = 𝓝 p := by
    simpa [c] using map_extChartAt_symm_nhdsWithin_range (I := 𝓡 n) p
  have hfreq' : ∃ᶠ y in 𝓝 (c p), f =ᶠ[𝓝 (c.symm y)] k := by
    rw [← hcmap] at hfreq
    exact hfreq
  have hfreqd : ∃ᶠ y in 𝓝 (c p), fderiv ℝ F y = fderiv ℝ K y := by
    apply (hfreq'.and_eventually
      (extChartAt_target_mem_nhds' (mem_extChartAt_target p))).mono
    intro y hy
    have hc : ContinuousAt c.symm y :=
      (continuousOn_extChartAt_symm p y hy.2).continuousAt
        (extChartAt_target_mem_nhds' hy.2)
    exact ((hy.1.comp_tendsto hc).fun_comp d).fderiv_eq
  have hd := tendsto_nhds_unique_of_frequently_eq
    (hF.fderiv_right (m := ∞) (by simp)).continuousAt
    (hK.fderiv_right (m := ∞) (by simp)).continuousAt hfreqd
  have hdf : mfderiv (𝓡 n) (𝓡 n) f p = fderiv ℝ F (c p) := by
    rw [mfderiv, if_pos (hf.mdifferentiableAt (by simp))]
    simp [F, c, d, writtenInExtChartAt]
  have hdk : mfderiv (𝓡 n) (𝓡 n) k p = fderiv ℝ K (c p) := by
    rw [mfderiv, if_pos (hk.mdifferentiableAt (by simp))]
    simp [K, c, d, hpos, writtenInExtChartAt]
  exact hdf.trans (hd.trans hdk.symm)

theorem local_isometry_eqOn_of_firstOrder [T2Space M] [CompactSpace M] [T2Space N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f k : M → N} {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hk : ContMDiffOn (𝓡 n) (𝓡 n) ∞ k U)
    (hfmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w))
    (hkmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (k x)
        (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w))
    {p : M} (hp : p ∈ U) (hpos : f p = k p)
    (hder : mfderiv (𝓡 n) (𝓡 n) f p = mfderiv (𝓡 n) (𝓡 n) k p) :
    EqOn f k U := by
  let G : Set M := {x | f =ᶠ[𝓝 x] k}
  have hGo : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hpG : p ∈ G := local_isometry_germ_ext g h hU hf hk hfmetric hkmetric hp hpos hder
  have hGc : closure G ∩ U ⊆ G := by
    intro x hx
    have hfreq : ∃ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] k := mem_closure_iff_frequently.mp hx.1
    have hfx := hf.contMDiffAt (hU.mem_nhds hx.2)
    have hkx := hk.contMDiffAt (hU.mem_nhds hx.2)
    have hval : f x = k x := tendsto_nhds_unique_of_frequently_eq
      hfx.continuousAt hkx.continuousAt (hfreq.mono fun y hy => hy.self_of_nhds)
    exact local_isometry_germ_ext g h hU hf hk hfmetric hkmetric hx.2 hval
      (mfderiv_eq_of_frequently_equal_germs hfx hkx hval hfreq)
  have hsub := hUc.subset_of_closure_inter_subset hGo ⟨p, hp, hpG⟩ hGc
  exact fun x hx => (hsub hx).self_of_nhds

end PoincareConjecture.SpaceForm
