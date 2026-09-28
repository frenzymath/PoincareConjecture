import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialJacobi
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.FixedChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.Variation








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter
open scoped ContDiff Topology Manifold Bundle

namespace PoincareConjecture.ConnectionVariation

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem manifoldVariation_jacobi
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {S I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I) (h0 : (0 : ℝ) ∈ S)
    {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ u (S ×ˢ I))
    (hgeo : ∀ s ∈ S, RiemannianMetric.IsGeodesicOn g (fun t => u (s, t)) I)
    {t : ℝ} (ht : t ∈ I) :
    let γ : ℝ → M := fun τ => u (0, τ)
    let J : (τ : ℝ) → TangentSpace (𝓡 n) (γ τ) :=
      fun τ => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => u (s, τ)) 0 1
    manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t +
      D.curvature (γ t) (J t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 0 := by
  let γ : ℝ → M := fun τ => u (0, τ)
  let J : (τ : ℝ) → TangentSpace (𝓡 n) (γ τ) :=
    fun τ => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => u (s, τ)) 0 1
  let a := γ t
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let q := c ∘ u
  have hut := hu.contMDiffAt ((hS.prod hI).mem_nhds (show (0, t) ∈ S ×ˢ I from ⟨h0, ht⟩))
  have hnear : (S ×ˢ I) ∩ u ⁻¹' c.source ∈ 𝓝 (0, t) :=
    inter_mem ((hS.prod hI).mem_nhds ⟨h0, ht⟩)
      (hut.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a)))
  obtain ⟨S', I', hS', h0', hI', ht', hsub⟩ := mem_nhds_prod_iff'.mp hnear
  have hmem {s r : ℝ} (hs : s ∈ S') (hr : r ∈ I') :
      u (s, r) ∈ c.source := (hsub ⟨hs, hr⟩).2
  have hu' {s r : ℝ} (hs : s ∈ S') (hr : r ∈ I') :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ u (s, r) :=
    hu.contMDiffAt ((hS.prod hI).mem_nhds (hsub ⟨hs, hr⟩).1)
  have hq {s r : ℝ} (hs : s ∈ S') (hr : r ∈ I') : ContDiffAt ℝ ∞ q (s, r) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hmem hs hr)).comp
      (s, r) (hu' hs hr)
  let T : ℝ × ℝ → EuclideanSpace ℝ (Fin n) := fun p => fderiv ℝ q p (0, 1)
  have hT {s r : ℝ} (hs : s ∈ S') (hr : r ∈ I') : ContDiffAt ℝ ∞ T (s, r) :=
    ((hq hs hr).fderiv_right (by simp)).clm_apply contDiffAt_const
  have hTderiv {s r : ℝ} (hs : s ∈ S') (hr : r ∈ I') :
      T (s, r) = deriv (fun τ => q (s, τ)) r := by
    have hd := ((hq hs hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_const r s).prodMk (hasDerivAt_id r))
    exact hd.deriv.symm
  let G : GeodesicVariation B S' I' := {
    phase := fun p => (q p, T p)
    smooth := fun p hp => ((hq hp.1 hp.2).prodMk (hT hp.1 hp.2)).contDiffWithinAt
    base_mem := h0'
    geodesic := by
      intro s hs r hr
      have hg : g.IsGeodesicOn (fun τ => u (s, τ)) I' := by
        intro τ hτ
        have hm := (hsub (show (s, τ) ∈ S' ×ˢ I' from ⟨hs, hτ⟩)).1
        exact hgeo s hm.1 τ hm.2
      have hd := hg.hasDerivAt_in_chart hI' a (fun τ hτ => hmem hs hτ) r hr
      have heq : (fun τ => T (s, τ)) =ᶠ[𝓝 r] deriv (fun τ => q (s, τ)) := by
        filter_upwards [hI'.mem_nhds hr] with τ hτ
        exact hTderiv hs hτ
      have hw := hd.2.congr_of_eventuallyEq heq
      have hp := hd.1
      change HasDerivAt (fun τ => q (s, τ)) (deriv (fun τ => q (s, τ)) r) r at hp
      change HasDerivAt (fun τ => T (s, τ))
        (-coordinateChristoffel B (q (s, r)) (deriv (fun τ => q (s, τ)) r)
          (deriv (fun τ => q (s, τ)) r)) r at hw
      rw [← hTderiv hs hr] at hp hw
      exact hp.prodMk hw }
  have hG := geodesicVariation_jacobi (isOpen_extChartAt_target a)
    (g.contDiffOn_chartCoefficients a) (fun x hx => g.isInvertible_chartCoefficients a hx)
    (fun x _ v w => g.symm _ _ _) hS' hI' h0' G
    (fun s hs r hr => c.map_source (hmem hs hr)) t ht'
  let Q : ℝ → EuclideanSpace ℝ (Fin n) := fun r => q (0, r)
  let V : ℝ → EuclideanSpace ℝ (Fin n) := variationField G
  let V' : ℝ → EuclideanSpace ℝ (Fin n) := covDerivAlong (christoffelBilinear B) Q V 1
  have hQ {r : ℝ} (hr : r ∈ I') : ContDiffAt ℝ ∞ Q r :=
    (hq h0' hr).comp r (contDiffAt_const.prodMk contDiffAt_id)
  have hV {r : ℝ} (hr : r ∈ I') : ContDiffAt ℝ ∞ V r :=
    (G.contDiffOn_variationField hS' hI').contDiffAt (hI'.mem_nhds hr)
  have hγ {r : ℝ} (hr : r ∈ I') : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ r :=
    (hu' h0' hr).comp r
      (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_const.prodMk contDiffAt_id))
  have hJ {r : ℝ} (hr : r ∈ I') :
      mfderiv (𝓡 n) (𝓡 n) c (γ r) (J r) = V r := by
    have hsmooth : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun s => u (s, r)) 0 :=
      (hu' h0' hr).comp 0
        (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_id.prodMk contDiffAt_const))
    have hd := mfderiv_comp 0 (mdifferentiableAt_extChartAt
      (by simpa only [c, extChartAt_source] using hmem h0' hr))
      (hsmooth.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact (congrArg (fun L => L 1) hd).symm
  have hJnear {r : ℝ} (hr : r ∈ I') :
      (fun τ => mfderiv (𝓡 n) (𝓡 n) c (γ τ) (J τ)) =ᶠ[𝓝 r] V := by
    filter_upwards [hI'.mem_nhds hr] with τ hτ
    exact hJ hτ
  have hV' {r : ℝ} (hr : r ∈ I') : ContDiffAt ℝ ∞ V' r :=
    contDiffAt_covDerivAlong (u := Q) (V := V)
      (contDiffAt_christoffelBilinear
        ((g.contDiffOn_chartCoefficients a).contDiffAt
          ((isOpen_extChartAt_target a).mem_nhds (c.map_source (hmem h0' hr))))
        (g.isInvertible_chartCoefficients a (c.map_source (hmem h0' hr)))) (hQ hr) (hV hr) 1
  have hDJ {r : ℝ} (hr : r ∈ I') :
      mfderiv (𝓡 n) (𝓡 n) c (γ r) (manifoldCovDerivAlong g γ J 1 r) = V' r := by
    rw [manifoldCovDerivAlong_in_chart (u := γ) (V := J) g a (hmem h0' hr) (hγ hr).continuousAt
      ((hQ hr).differentiableAt (by simp))
      (((hV hr).differentiableAt (by simp)).congr_of_eventuallyEq (by
        simpa [c] using hJnear hr))]
    exact covDerivAlong_congr _ _ (hJnear hr) 1
  have hDJnear : (fun r => mfderiv (𝓡 n) (𝓡 n) c (γ r)
      (manifoldCovDerivAlong g γ J 1 r)) =ᶠ[𝓝 t] V' := by
    filter_upwards [hI'.mem_nhds ht'] with r hr
    exact hDJ hr
  have hDDJ : mfderiv (𝓡 n) (𝓡 n) c (γ t)
      (manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t) =
      covDerivAlong (christoffelBilinear B) Q V' 1 t := by
    rw [manifoldCovDerivAlong_in_chart (u := γ) (V := manifoldCovDerivAlong g γ J 1)
      g a (hmem h0' ht') (hγ ht').continuousAt
      ((hQ ht').differentiableAt (by simp))
      (((hV' ht').differentiableAt (by simp)).congr_of_eventuallyEq (by
        simpa [c] using hDJnear))]
    exact covDerivAlong_congr _ _ hDJnear 1
  have hvelocity : mfderiv (𝓡 n) (𝓡 n) c (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = T (0, t) := by
    have hd := mfderiv_comp t (mdifferentiableAt_extChartAt
      (by simpa only [c, extChartAt_source] using hmem h0' ht'))
      ((hγ ht').mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    have hd1 := congrArg (fun L => L 1) hd
    rw [hTderiv h0' ht']
    exact hd1.symm
  apply (isInvertible_mfderiv_extChartAt (hmem h0' ht')).injective
  rw [map_add, map_zero, hDDJ]
  rw [← coordinateCurvature_in_chart g D a (hmem h0' ht'), hJ ht', hvelocity]
  exact hG









noncomputable def manifoldRadialVariation
    (g : RiemannianMetric n M) (a : M)
    {D : LocalFlowData (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a).target (extChartAt (𝓡 n) a a)}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ D.domain) (w : EuclideanSpace ℝ (Fin n))
    (s t : ℝ) : M :=
    (extChartAt (𝓡 n) a).symm
    ((D.radialGeodesicVariation hv w).phase (s, t)).1

theorem manifoldRadialVariation_initial
    (g : RiemannianMetric n M) (a : M)
    {D : LocalFlowData (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a).target (extChartAt (𝓡 n) a a)}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ D.domain) (w : EuclideanSpace ℝ (Fin n)) :
    manifoldRadialVariation g a hv w 0 0 = a := by
  let c := extChartAt (𝓡 n) a
  have htraj := D.trajectory_initial hv
  change c.symm ((D.radialGeodesicVariation hv w).phase (0, 0)).1 = a
  simpa [CoordinateExponential.LocalFlowData.radialGeodesicVariation,
    c] using congrArg c.symm (congrArg Prod.fst htraj)

theorem manifoldRadialVariation_initial_deriv
    (g : RiemannianMetric n M) (a : M)
    {D : LocalFlowData (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a).target (extChartAt (𝓡 n) a a)}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ D.domain) (w : EuclideanSpace ℝ (Fin n)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun s => manifoldRadialVariation g a hv w s 0) 0 1 = 0 := by
  let c := extChartAt (𝓡 n) a
  have hline : ContinuousAt (fun s : ℝ => v + s • w) 0 := by fun_prop
  have hdom : ∀ᶠ s in 𝓝 (0 : ℝ), v + s • w ∈ D.domain :=
    hline.preimage_mem_nhds (D.isOpen_domain.mem_nhds (by simpa using hv))
  have hconst : (fun s => manifoldRadialVariation g a hv w s 0) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => a) := by
    filter_upwards [hdom] with s hs
    change c.symm ((D.radialGeodesicVariation hv w).phase (s, 0)).1 = a
    simpa [CoordinateExponential.LocalFlowData.radialGeodesicVariation, c] using
      congrArg c.symm (congrArg Prod.fst (D.trajectory_initial hs))
  rw [hconst.mfderiv_eq]
  simp

set_option maxHeartbeats 200000 in
theorem manifoldRadialVariation_initial_covariantDerivative
    (g : RiemannianMetric n M) (a : M)
    {D : LocalFlowData (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a).target (extChartAt (𝓡 n) a a)}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ D.domain) (w : EuclideanSpace ℝ (Fin n)) :
    manifoldCovDerivAlong g
        (fun t => manifoldRadialVariation g a hv w 0 t)
        (fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
          (fun s => manifoldRadialVariation g a hv w s t) 0 1) 1 0 =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm
        (extChartAt (𝓡 n) a a) w := by
  let c := extChartAt (𝓡 n) a
  let γ : ℝ → M := fun t => manifoldRadialVariation g a hv w 0 t
  let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s => manifoldRadialVariation g a hv w s t) 0 1
  let V : ℝ → EuclideanSpace ℝ (Fin n) :=
    variationField (D.radialGeodesicVariation hv w)
  have hVeq {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
      mfderiv (𝓡 n) (𝓡 n) c (γ t) (J t) = V t := by
    have htarget : ((D.radialGeodesicVariation hv w).phase (0, t)).1 ∈ c.target :=
      D.radialGeodesicVariation_stays hv w
        (D.zero_mem_radialParameterDomain hv w) ht
    have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm
        ((D.radialGeodesicVariation hv w).phase (0, t)).1 :=
      (mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 n) htarget).mdifferentiableAt
        (by simp only [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
    have hq : ContDiffAt ℝ ∞
        (fun s : ℝ => ((D.radialGeodesicVariation hv w).phase (s, t)).1) 0 := by
      have hq' : ContDiffAt ℝ ∞ (D.radialGeodesicVariation hv w).phase (0, t) :=
        (D.radialGeodesicVariation hv w).smooth.contDiffAt
        (((D.isOpen_radialParameterDomain v w).prod isOpen_Ioo).mem_nhds
          ⟨D.zero_mem_radialParameterDomain hv w, ht⟩)
      exact ContDiffAt.comp (f := fun s : ℝ => (s, t))
        (g := fun p => ((D.radialGeodesicVariation hv w).phase p).1) 0
        hq'.fst (contDiffAt_id.prodMk contDiffAt_const)
    have hcomp := mfderiv_comp 0 hc (hq.differentiableAt (by simp)).mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hcomp
    have hJ : J t = mfderiv (𝓡 n) (𝓡 n) c.symm
        ((D.radialGeodesicVariation hv w).phase (0, t)).1 (V t) := by
      exact congrArg (fun L => L 1) hcomp
    rw [hJ]
    have hinv := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := 𝓡 n) htarget
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hinv
    exact congrArg (fun L => L (V t)) hinv
  have hγ0 : γ 0 = a := by
    exact manifoldRadialVariation_initial g a hv w
  have hVnear : (fun t => mfderiv (𝓡 n) (𝓡 n) c (γ t) (J t)) =ᶠ[𝓝 0] V := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-2 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 2)] with t ht
    exact hVeq ht
  change manifoldCovDerivAlong g γ J 1 0 = _
  unfold manifoldCovDerivAlong
  rw [hγ0]
  change (mfderiv (𝓡 n) (𝓡 n) c a).inverse
    (covDerivAlong (christoffelBilinear (g.pullbackCoefficients c.symm))
      (c ∘ γ) (fun t => mfderiv (𝓡 n) (𝓡 n) c (γ t) (J t)) 1 0) = _
  rw [covDerivAlong_congr _ _ hVnear, covDerivAlong]
  have hzero : V 0 = 0 := D.radialGeodesicVariation_initial hv w
  have hderiv : fderiv ℝ V 0 1 = w := D.radialGeodesicVariation_initial_deriv hv w
  rw [hzero, hderiv, map_zero, add_zero]
  apply (isInvertible_mfderiv_extChartAt (I := 𝓡 n) (mem_extChartAt_source a)).injective
  rw [(isInvertible_mfderiv_extChartAt (I := 𝓡 n) (mem_extChartAt_source a)).self_apply_inverse]
  have hinv := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := 𝓡 n) (mem_extChartAt_source a)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hinv
  exact (congrArg (fun L => L w) hinv).symm

theorem manifoldRadialVariation_endpoint
    (g : RiemannianMetric n M) (a : M)
    {D : LocalFlowData (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a).target (extChartAt (𝓡 n) a a)}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ D.domain) (w : EuclideanSpace ℝ (Fin n)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun s => manifoldRadialVariation g a hv w s 1) 0 1 =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm (D.exponential v)
        (fderiv ℝ D.exponential v w) := by
  let c := extChartAt (𝓡 n) a
  have htarget : D.exponential v ∈ c.target := by
    rw [← D.trajectory_endpoint]
    exact D.trajectory_mem hv (by norm_num)
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (D.exponential v) :=
    (mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 n) htarget).mdifferentiableAt
      (by simp only [ModelWithCorners.range_eq_univ]; exact Filter.univ_mem)
  let r : ℝ → EuclideanSpace ℝ (Fin n) := fun s => D.exponential (v + s • w)
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hd := (D.smooth_exponential.contDiffAt
    (D.isOpen_domain.mem_nhds hv)).differentiableAt (by simp)
  have hr : HasDerivAt r (fderiv ℝ D.exponential v w) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hc' : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (r 0) := by
    simpa only [r, zero_smul, add_zero] using hc
  have hcomp := mfderiv_comp 0 hc' hr.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hcomp
  have hrewrite : (fun s => manifoldRadialVariation g a hv w s 1) =
      c.symm ∘ r := by
    funext s
    exact congrArg c.symm (D.trajectory_endpoint (v + s • w))
  rw [hrewrite, hcomp]
  change mfderiv (𝓡 n) (𝓡 n) c.symm (r 0) (fderiv ℝ r 0 1) = _
  rw [fderiv_eq_smul_deriv, one_smul, hr.deriv]
  exact congrArg (fun y => mfderiv (𝓡 n) (𝓡 n) c.symm y
    (fderiv ℝ D.exponential v w)) (by simp [r])


end PoincareConjecture.ConnectionVariation
