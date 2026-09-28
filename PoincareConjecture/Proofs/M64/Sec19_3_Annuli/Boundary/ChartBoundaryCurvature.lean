import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteChartDifferential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularTraceChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundarySubdivision







noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace M65Gauss

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1200000 in






theorem halfDisk_chart_boundary_connection (D : LeviCivitaData g)
    {f : E → M} {S : Set E} (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) 1 f S)
    (p : M) (e : ℂ ≃L[ℝ] E) (a : E)
    (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (DE : LeviCivitaData gE)
    {R : ℝ} (hR : 0 < R) (Q : ℂ → Fin n → ℂ)
    {c : ℝ → M} {label : ℝ → ℝ} (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ c)
    (hcv : ∀ s, curveVelocity (n := n) c s ≠ 0) (hlabel : ContDiff ℝ 1 label)
    (hmono : Monotone label ∨ Antitone label)
    (htrace : ∀ t : ℝ, f (a + e (t : ℂ)) = c (label t)) :
    let q := chartAt (EuclideanSpace ℝ (Fin n)) p
    let P := fun z => a + e z
    let H := q ∘ f ∘ P
    let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
    let V := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
    let kappa := fun s => (g.tangentNorm (c s) (curveVelocity (n := n) c s))⁻¹ •
      rampHorizontalCovariantDerivative D c
        (fun y => (g.tangentNorm (c y) (curveVelocity (n := n) c y))⁻¹ •
          curveVelocity (n := n) c y) s
    MapsTo P K S → MapsTo (f ∘ P) K q.source → ContDiffOn ℝ 1 H K →
      (∀ z ∈ K, gE.euclideanCoefficients =ᶠ[𝓝 (H z)] g.pullbackCoefficients q.symm) →
      (∀ z ∈ K, halfDiskGradient H R z = Q z) → ContinuousOn V K →
      (∀ z ∈ K, gE.inner (H z) (V z).1 (V z).1 = 1) →
      ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 1 (fun s : ℝ => (V (s : ℂ)).1) t ∧
        gE.inner (H (t : ℂ))
          (deriv (fun s : ℝ => (V (s : ℂ)).1) t +
            connectionCoefficient DE (H (t : ℂ))
              (fderivWithin ℝ H K (t : ℂ) 1) (V (t : ℂ)).1) (V (t : ℂ)).2 =
          g.inner (f (P (t : ℂ))) (kappa (label t))
            (mfderivWithin 𝓘(ℝ, E) (𝓡 n) f S (P (t : ℂ)) (e I)) := by
  let q := chartAt (EuclideanSpace ℝ (Fin n)) p
  let P := fun z => a + e z
  let H := q ∘ f ∘ P
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let V := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
  let cc := q ∘ c
  let T := fun s => (Real.sqrt (gE.inner (cc s) (deriv cc s) (deriv cc s)))⁻¹ • deriv cc s
  let kc := fun s => (Real.sqrt (gE.inner (cc s) (deriv cc s) (deriv cc s)))⁻¹ •
    (deriv T s + connectionCoefficient DE (cc s) (deriv cc s) (T s))
  let kappa := fun s => (g.tangentNorm (c s) (curveVelocity (n := n) c s))⁻¹ •
    rampHorizontalCovariantDerivative D c
      (fun y => (g.tangentNorm (c y) (curveVelocity (n := n) c y))⁻¹ •
        curveVelocity (n := n) c y) s
  change MapsTo P K S → MapsTo (f ∘ P) K q.source → ContDiffOn ℝ 1 H K → _
  intro hP hsource hH hmetric hgradient hV hunit
  have hK0 : (0 : ℂ) ∈ K := ⟨mem_closedBall_self hR.le, by simp⟩
  have hsrc0 : c (label 0) ∈ q.source := by
    rw [← htrace 0]
    exact hsource hK0
  obtain ⟨hJ, hJ0, hcc, hccv⟩ := regular_trace_in_chart hc p hsrc0 (hcv (label 0))
  have hfactor (z : ℂ) (hz : z ∈ K) : halfDiskGradient H R z = z ^ (0 : ℕ) • Q z := by
    simpa only [pow_zero, one_smul] using hgradient z hz
  have hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = cc (label t) :=
    Filter.Eventually.of_forall (fun t => congrArg q (htrace t))
  have hlocal := halfDisk_boundary_connection_curvature DE hR (show Even 0 from ⟨0, rfl⟩)
    hH hfactor hV hunit ((hcc.contDiffAt (hJ.mem_nhds hJ0)).of_le
      (WithTop.coe_le_coe.mpr le_top)) hccv hlabel hmono hcurve
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ < R :=
    continuous_ofReal.norm.continuousAt.eventually (gt_mem_nhds (by simpa using hR))
  filter_upwards [hlocal, hnear] with t ht htball
  have hKt : (t : ℂ) ∈ K := ⟨mem_closedBall_zero_iff.mpr htball.le, by simp⟩
  have hsrc : f (P (t : ℂ)) ∈ q.source := hsource hKt
  have hvalue : H (t : ℂ) = cc (label t) := congrArg q (htrace t)
  have hsrcCurve : c (label t) ∈ q.source := by rw [← htrace t]; exact hsrc
  have hmet : ∀ᶠ y in 𝓝 (H (t : ℂ)), ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = g.inner (q.symm y)
        (mfderiv (𝓡 n) (𝓡 n) q.symm y u) (mfderiv (𝓡 n) (𝓡 n) q.symm y v) := by
    filter_upwards [hmetric (t : ℂ) hKt] with y hy u v
    change gE.euclideanCoefficients y u v = _
    rw [hy]
    rfl
  have hmetc : ∀ᶠ y in 𝓝 (cc (label t)), ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = g.inner (q.symm y)
        (mfderiv (𝓡 n) (𝓡 n) q.symm y u) (mfderiv (𝓡 n) (𝓡 n) q.symm y v) := by
    rw [← hvalue]
    exact hmet
  have htransport := regular_curve_curvature_chart D DE p hc hcv hsrcCurve hmetc
  have hpushK : (mfderiv (𝓡 n) (𝓡 n) q.symm (H (t : ℂ)) (kc (label t)) :
      EuclideanSpace ℝ (Fin n)) = kappa (label t) := by
    change (kappa (label t) : EuclideanSpace ℝ (Fin n)) =
      mfderiv (𝓡 n) (𝓡 n) q.symm (cc (label t)) (kc (label t)) at htransport
    exact (congrArg (fun y => (mfderiv (𝓡 n) (𝓡 n) q.symm y (kc (label t)) :
      EuclideanSpace ℝ (Fin n))) hvalue).trans htransport.symm
  let L := fderivWithin ℝ H K (t : ℂ)
  let N := mfderivWithin 𝓘(ℝ, E) (𝓡 n) f S (P (t : ℂ)) (e I)
  have hchain : L I = mfderiv (𝓡 n) (𝓡 n) q (f (P (t : ℂ))) N := by
    exact congrArg (fun A => A I) (within_chart_affine_derivative p e a
      ((hf _ (hP hKt)).mdifferentiableWithinAt one_ne_zero)
      ((halfDisk_differential_domain hR).2.2.1 _ hKt) hP hsrc)
  have hpushI : (mfderiv (𝓡 n) (𝓡 n) q.symm (H (t : ℂ)) (L I) :
      EuclideanSpace ℝ (Fin n)) = N := by
    rw [hchain]
    exact congrArg (fun A : TangentSpace (𝓡 n) (f (P (t : ℂ))) →L[ℝ]
      TangentSpace (𝓡 n) (f (P (t : ℂ))) => A N)
      ((mdifferentiable_chart (I := 𝓡 n) p).symm_comp_deriv hsrc)
  have hpair := hmet.self_of_nhds (kc (label t)) (L I)
  have hinv : q.symm (H (t : ℂ)) = f (P (t : ℂ)) := q.left_inv hsrc
  rw [hinv] at hpair
  have hpair' : gE.inner (H (t : ℂ)) (kc (label t)) (L I) =
      g.inner (f (P (t : ℂ))) (kappa (label t)) N := by
    exact hpair.trans (congrArg₂ (fun u v : EuclideanSpace ℝ (Fin n) =>
      g.inner (f (P (t : ℂ))) u v) hpushK hpushI)
  exact ⟨ht.1, ht.2.trans hpair'⟩

end PoincareConjecture.M64
