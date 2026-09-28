import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.CircleRelabeling
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskConformal
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceTangentExtension
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryArc
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible









set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold Bundle intervalIntegral

namespace PoincareConjecture.M65Filling

private theorem angular_covering : IsCoveringMap m65LoopAngular := by
  have h := (AddCircle.isCoveringMap_coe (2 * Real.pi)).homeomorph_comp m65AngleLoopCircle
  convert! h using 1
  funext x
  exact (m65AngleLoopCircle_coe x).symm

private theorem angular_eq_iff (x y : ℝ) :
    m65LoopAngular x = m65LoopAngular y ↔ ∃ n : ℤ, x = y + n * (2 * Real.pi) := by
  have he : m65LoopAngular x = m65LoopAngular y ↔ Circle.exp x = Circle.exp y := by
    unfold m65LoopAngular
    rw [← m65AngleLoopCircle_coe x, ← m65AngleLoopCircle_coe y]
    constructor
    · intro h
      exact congrArg AddCircle.homeomorphCircle' (m65AngleLoopCircle.injective h)
    · intro h
      apply congrArg m65AngleLoopCircle
      exact AddCircle.homeomorphCircle'.injective h
  exact he.trans Circle.exp_eq_exp

private theorem angular_periodic : Function.Periodic m65LoopAngular (2 * Real.pi) := by
  intro x
  exact (angular_eq_iff _ _).mpr ⟨1, by simp⟩

private theorem circle_homeomorph_lift (beta : LoopCircle ≃ₜ LoopCircle) :
    ∃ h : ℝ ≃ₜ ℝ, ∀ x : ℝ, m65LoopAngular (h x) = beta (m65LoopAngular x) := by
  let f : C(ℝ, LoopCircle) := ⟨fun x => beta (m65LoopAngular x),
    beta.continuous.comp m65LoopAngular_continuous_surjective.1⟩
  obtain ⟨y, hy⟩ := m65LoopAngular_continuous_surjective.2 (f 0)
  obtain ⟨h, ⟨h0, hh⟩, _⟩ := angular_covering.existsUnique_continuousMap_lifts f 0 y hy
  have hhx (x : ℝ) : m65LoopAngular (h x) = beta (m65LoopAngular x) := congrFun hh x
  let f' : C(ℝ, LoopCircle) := ⟨fun x => beta.symm (m65LoopAngular x),
    beta.symm.continuous.comp m65LoopAngular_continuous_surjective.1⟩
  obtain ⟨g, ⟨g0, hg⟩, _⟩ := angular_covering.existsUnique_continuousMap_lifts f' y 0 (by
    change m65LoopAngular 0 = beta.symm (m65LoopAngular y)
    rw [hy]
    exact (beta.symm_apply_apply _).symm)
  have hgx (x : ℝ) : m65LoopAngular (g x) = beta.symm (m65LoopAngular x) := congrFun hg x
  have hgh : (fun x => g (h x)) = id := angular_covering.eq_of_comp_eq
    (g.continuous.comp h.continuous) continuous_id (by
      funext x
      change m65LoopAngular (g (h x)) = m65LoopAngular x
      rw [hgx, hhx, beta.symm_apply_apply]) 0 (by simp only [h0, g0, id_eq])
  have hhg : (fun x => h (g x)) = id := angular_covering.eq_of_comp_eq
    (h.continuous.comp g.continuous) continuous_id (by
      funext x
      change m65LoopAngular (h (g x)) = m65LoopAngular x
      rw [hhx, hgx, beta.apply_symm_apply]) y (by simp only [h0, g0, id_eq])
  exact ⟨{
    toFun := h
    invFun := g
    left_inv := congrFun hgh
    right_inv := congrFun hhg
    continuous_toFun := h.continuous
    continuous_invFun := g.continuous }, hhx⟩

private theorem real_homeomorph_orientation (h : ℝ ≃ₜ ℝ) : StrictMono h ∨ StrictAnti h := by
  have hi := h.continuous.continuousOn.strictMonoOn_of_injOn_Icc'
    (show (0 : ℝ) ≤ 1 by norm_num) h.injective.injOn
  rcases hi with hi | hi
  · exact Or.inl (h.continuous.strictMonoOn_of_inj_rigidity h.injective (by norm_num) hi)
  · right
    have hn : StrictMonoOn (fun x : ℝ => -h x) (Icc 0 1) := fun x hx y hy hxy =>
      neg_lt_neg (hi hx hy hxy)
    have hni : Function.Injective (fun x : ℝ => -h x) := neg_injective.comp h.injective
    have hm := h.continuous.neg.strictMonoOn_of_inj_rigidity hni (by norm_num) hn
    intro x y hxy
    exact neg_lt_neg_iff.mp (hm hxy)

private theorem increasing_lift_period
    (beta : LoopCircle ≃ₜ LoopCircle) (h : ℝ → ℝ) (hc : Continuous h) (hm : StrictMono h)
    (he : ∀ x : ℝ, m65LoopAngular (h x) = beta (m65LoopAngular x)) (x : ℝ) :
    h (x + 2 * Real.pi) = h x + 2 * Real.pi := by
  have hP : 0 < 2 * Real.pi := by positivity
  have hinc : h x < h (x + 2 * Real.pi) := hm (by linarith)
  have heq : m65LoopAngular (h (x + 2 * Real.pi)) = m65LoopAngular (h x) := by
    rw [he, he, angular_periodic x]
  obtain ⟨n, hn⟩ := (angular_eq_iff _ _).mp heq
  have hnposR : (0 : ℝ) < n := by nlinarith
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hnposR
  have hn1 : (1 : ℤ) ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hle : h x + 2 * Real.pi ≤ h (x + 2 * Real.pi) := by nlinarith
  apply le_antisymm _ hle
  by_contra! hgt
  obtain ⟨y, hy, hhy⟩ := intermediate_value_Ioo (by linarith : x ≤ x + 2 * Real.pi)
    hc.continuousOn ⟨by linarith, hgt⟩
  have hyeq : m65LoopAngular y = m65LoopAngular x := by
    apply beta.injective
    rw [← he y, ← he x, hhy, angular_periodic (h x)]
  obtain ⟨m, hmy⟩ := (angular_eq_iff _ _).mp hyeq
  have hm0 : (0 : ℝ) < m := by nlinarith [hy.1]
  have hm1 : (m : ℝ) < 1 := by nlinarith [hy.2]
  have hm0Z : (0 : ℤ) < m := by exact_mod_cast hm0
  have hm1Z : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

private theorem decreasing_lift_period
    (beta : LoopCircle ≃ₜ LoopCircle) (h : ℝ → ℝ) (hc : Continuous h) (hm : StrictAnti h)
    (he : ∀ x : ℝ, m65LoopAngular (h x) = beta (m65LoopAngular x)) (x : ℝ) :
    h (x + 2 * Real.pi) = h x - 2 * Real.pi := by
  have hP : 0 < 2 * Real.pi := by positivity
  have hinc : h (x + 2 * Real.pi) < h x := hm (by linarith)
  have heq : m65LoopAngular (h (x + 2 * Real.pi)) = m65LoopAngular (h x) := by
    rw [he, he, angular_periodic x]
  obtain ⟨n, hn⟩ := (angular_eq_iff _ _).mp heq
  have hnnegR : (n : ℝ) < 0 := by nlinarith
  have hnneg : n < (0 : ℤ) := by exact_mod_cast hnnegR
  have hn1 : n ≤ (-1 : ℤ) := by omega
  have hn1R : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
  have hle : h (x + 2 * Real.pi) ≤ h x - 2 * Real.pi := by nlinarith
  apply le_antisymm hle
  by_contra! hlt
  obtain ⟨y, hy, hhy⟩ := intermediate_value_Ioo' (by linarith : x ≤ x + 2 * Real.pi)
    hc.continuousOn ⟨hlt, by linarith⟩
  have hyeq : m65LoopAngular y = m65LoopAngular x := by
    apply beta.injective
    rw [← he y, ← he x, hhy, angular_periodic.sub_eq (h x)]
  obtain ⟨m, hmy⟩ := (angular_eq_iff _ _).mp hyeq
  have hm0 : (0 : ℝ) < m := by nlinarith [hy.1]
  have hm1 : (m : ℝ) < 1 := by nlinarith [hy.2]
  have hm0Z : (0 : ℤ) < m := by exact_mod_cast hm0
  have hm1Z : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

set_option backward.isDefEq.respectTransparency false in
private theorem lift_contDiff_of_regular_curve
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] (c eta : ℝ → M) (h : ℝ → ℝ)
    (hc : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ c)
    (hreg : ∀ x, curveVelocity (n := 3) c x ≠ 0)
    (heta : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 1 eta) (hh : Continuous h)
    (he : ∀ x, eta x = c (h x)) : ContDiff ℝ 1 h := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let q := chartAt LoopAmbient (c (h x))
  let I := c ⁻¹' q.source
  let C := q ∘ c
  have hs : c (h x) ∈ q.source := mem_chart_source LoopAmbient _
  have hI : IsOpen I := q.open_source.preimage hc.continuous
  have hC : ContDiffOn ℝ ∞ C I :=
    (contMDiffOn_chart.comp hc.contMDiffOn (fun _ ht => ht)).contDiffOn
  have hqd := (mdifferentiable_chart (I := 𝓡 3) (c (h x))).mdifferentiableAt hs
  have hcd := (hc (h x)).mdifferentiableAt (by simp)
  have hchain := congrArg (fun L : ℝ →L[ℝ] LoopAmbient => L 1)
    (mfderiv_comp (h x) hqd hcd)
  have hd : deriv C (h x) = mfderiv (𝓡 3) (𝓡 3) q (c (h x))
      (curveVelocity c (h x)) := by
    simpa +instances only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      fderiv_apply_one_eq_deriv, curveVelocity, C] using! hchain
  have hdne : deriv C (h x) ≠ 0 := by
    intro hz
    apply hreg (h x)
    apply ((mdifferentiable_chart (I := 𝓡 3) (c (h x))).mfderiv hs).injective
    change mfderiv (𝓡 3) (𝓡 3) q (c (h x)) (curveVelocity c (h x)) =
      mfderiv (𝓡 3) (𝓡 3) q (c (h x)) 0
    rw [← hd, hz, map_zero]
  obtain ⟨j, U, J, sigma, V, hU, hJ, hCx, hhx, _, _, hsig, _, hinv, _⟩ :=
    M65StrictTrace.exists_smooth_tangent_extension hI hs hC hdne
  have hs' : eta x ∈ q.source := by rw [he x]; exact hs
  have hqe : ContDiffAt ℝ 1 (q ∘ eta) x :=
    ((contMDiffOn_chart.contMDiffAt (q.open_source.mem_nhds hs')).comp x (heta x)).contDiffAt
  have hsigAt : ContDiffAt ℝ 1 sigma (q (eta x)) := by
    rw [he x]
    exact (hsig.contDiffAt (hU.mem_nhds hCx)).of_le (by simp)
  have hlocal : h =ᶠ[𝓝 x] sigma ∘ q ∘ eta := by
    filter_upwards [hh.continuousAt.preimage_mem_nhds (hJ.mem_nhds hhx)] with y hy
    change h y = sigma (q (eta y))
    rw [he y]
    exact (hinv (h y) hy).symm
  exact (hsigAt.comp x hqe).congr_of_eventuallyEq hlocal

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {gamma : C1FreeLoopSpace (M := M)}




theorem boundary_lift (S : M65MinimalDisk g D gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ x, curveVelocity (n := 3) (periodicFreeLoop gamma) x ≠ 0) :
    ∃ h : ℝ ≃ₜ ℝ, ContDiff ℝ 1 h ∧
      (∀ x, S.disk.map (Proofs.M58.angularPoint x) = periodicFreeLoop gamma (h x)) ∧
      ((StrictMono h ∧ ∀ x, h (x + 2 * Real.pi) = h x + 2 * Real.pi) ∨
        (StrictAnti h ∧ ∀ x, h (x + 2 * Real.pi) = h x - 2 * Real.pi)) := by
  let beta : LoopCircle ≃ₜ LoopCircle := {
    toFun := S.disk.reparameterization.map
    invFun := S.disk.reparameterization.inverse
    left_inv := S.disk.reparameterization.left_inverse
    right_inv := S.disk.reparameterization.right_inverse
    continuous_toFun := S.disk.reparameterization.continuous_map
    continuous_invFun := S.disk.reparameterization.continuous_inverse }
  obtain ⟨h, hh⟩ := circle_homeomorph_lift beta
  have he (x : ℝ) : S.disk.map (Proofs.M58.angularPoint x) =
      periodicFreeLoop gamma (h x) := by
    change S.disk.map (m65LoopAngular x : LoopPlane) = _
    rw [S.disk.boundary_eq]
    change gamma (beta (m65LoopAngular x)) = _
    rw [← hh x]
    exact (gamma.boundary (m65LoopAngular (h x))).symm
  refine ⟨h, lift_contDiff_of_regular_curve (periodicFreeLoop gamma)
    (S.disk.map ∘ Proofs.M58.angularPoint) h hsmooth hregular
    S.boundary_curve_velocity.1 h.continuous he, he, ?_⟩
  rcases real_homeomorph_orientation h with hm | hm
  · exact Or.inl ⟨hm, increasing_lift_period beta h h.continuous hm hh⟩
  · exact Or.inr ⟨hm, decreasing_lift_period beta h h.continuous hm hh⟩

omit [T2Space M] in
private theorem shifted_loop_pathLength (g : RiemannianMetric 3 M)
    (gamma : C1FreeLoopSpace (M := M)) (s : ℝ) :
    g.pathELength (periodicFreeLoop gamma) s (s + 2 * Real.pi) =
      ENNReal.ofReal (freeLoopLength g gamma) := by
  rw [M04.pathELength_eq_ofReal_integral_pathSpeed g
    (Proofs.M58.contMDiff_periodicFreeLoop gamma) (by linarith [Real.pi_pos])]
  apply congrArg ENNReal.ofReal
  simpa only [rampPeriod, zero_add, M04.pathSpeed, freeLoopLength, curveVelocity] using
    (Proofs.M58.periodic_freeLoopSpeed g gamma).intervalIntegral_add_eq s 0

set_option backward.isDefEq.respectTransparency false in



theorem boundary_speed_integral (S : M65MinimalDisk g D gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ x, curveVelocity (n := 3) (periodicFreeLoop gamma) x ≠ 0) :
    (∫ theta in (-Real.pi)..Real.pi,
      g.tangentNorm (S.disk.map (Proofs.M58.angularPoint theta))
        (curveVelocity (n := 3) (S.disk.map ∘ Proofs.M58.angularPoint) theta)) =
      freeLoopLength g gamma := by
  obtain ⟨h, hC1, he, horient⟩ := boundary_lift S hsmooth hregular
  let eta := S.disk.map ∘ Proofs.M58.angularPoint
  have heta : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 1 eta := S.boundary_curve_velocity.1
  have heq : eta = periodicFreeLoop gamma ∘ (h : ℝ → ℝ) := funext he
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hlength : g.pathELength eta (-Real.pi) Real.pi =
      ENNReal.ofReal (freeLoopLength g gamma) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [heq]
    rcases horient with ⟨hm, hp⟩ | ⟨hm, hp⟩
    · have hl : g.pathELength (periodicFreeLoop gamma ∘ (h : ℝ → ℝ))
          (-Real.pi) Real.pi =
          g.pathELength (periodicFreeLoop gamma) (h (-Real.pi)) (h Real.pi) :=
        Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) hab (hm.monotone.monotoneOn _)
          (hC1.differentiable one_ne_zero).differentiableOn
          (hsmooth.mdifferentiable (by simp)).mdifferentiableOn
      have hend : h Real.pi = h (-Real.pi) + 2 * Real.pi := by
        simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hp (-Real.pi)
      rw [hl, hend]
      exact shifted_loop_pathLength g gamma _
    · have hl : g.pathELength (periodicFreeLoop gamma ∘ (h : ℝ → ℝ))
          (-Real.pi) Real.pi =
          g.pathELength (periodicFreeLoop gamma) (h Real.pi) (h (-Real.pi)) :=
        Manifold.pathELength_comp_of_antitoneOn (I := 𝓡 3) hab (hm.antitone.antitoneOn _)
          (hC1.differentiable one_ne_zero).differentiableOn
          (hsmooth.mdifferentiable (by simp)).mdifferentiableOn
      have hend : h (-Real.pi) = h Real.pi + 2 * Real.pi := by
        have hq := hp (-Real.pi)
        rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hq
        linarith
      rw [hl, hend]
      exact shifted_loop_pathLength g gamma _
  rw [M04.pathELength_eq_ofReal_integral_pathSpeed g heta hab] at hlength
  exact (ENNReal.ofReal_eq_ofReal_iff
    (intervalIntegral.integral_nonneg hab (fun _ _ => M04.pathSpeed_nonneg g eta _))
    (Proofs.M58.freeLoopLength_nonneg g gamma)).mp hlength

set_option backward.isDefEq.respectTransparency false in



theorem radial_norm_eq_boundary_speed (S : M65MinimalDisk g D gamma) (theta : ℝ) :
    g.tangentNorm (S.disk.map (Proofs.M58.angularPoint theta))
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta)) =
      g.tangentNorm (S.disk.map (Proofs.M58.angularPoint theta))
        (curveVelocity (n := 3) (S.disk.map ∘ Proofs.M58.angularPoint) theta) := by
  let z := Proofs.M58.angularPoint theta
  have hz : z ∈ loopDiskSet := by
    change ‖Proofs.M58.angularPoint theta - 0‖ ≤ 1
    rw [sub_zero, Proofs.M58.norm_angularPoint]
  have hsum (v : LoopPlane) :
      (∑ i : Fin 2, v i • S.boundaryColumn z i) =
        mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z v := by
    let L := mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet z
    have hh := congrArg L ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v)
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr, L,
      M65MinimalDisk.boundaryColumn] using hh
  have hn : ‖Proofs.M58.angularVector theta‖ ^ 2 = 1 := by
    simp [Proofs.M58.angularVector, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      Real.sin_sq_add_cos_sq]
  rw [S.boundary_curve_velocity.2 theta, hsum]
  unfold RiemannianMetric.tangentNorm
  rw [S.withinDifferential_inner_self hz, S.withinDifferential_inner_self hz,
    hn, Proofs.M58.norm_angularPoint, one_pow]




theorem radial_norm_integral (S : M65MinimalDisk g D gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ x, curveVelocity (n := 3) (periodicFreeLoop gamma) x ≠ 0) :
    IntervalIntegrable (fun theta =>
      g.tangentNorm (S.disk.map (Proofs.M58.angularPoint theta))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
          (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta)))
      MeasureTheory.volume (-Real.pi) Real.pi ∧
    (∫ theta in (-Real.pi)..Real.pi,
      g.tangentNorm (S.disk.map (Proofs.M58.angularPoint theta))
        (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
          (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))) =
      freeLoopLength g gamma := by
  simp_rw [radial_norm_eq_boundary_speed S]
  exact ⟨(M04.continuous_pathSpeed g S.boundary_curve_velocity.1).intervalIntegrable _ _,
    boundary_speed_integral S hsmooth hregular⟩

end PoincareConjecture.M65Filling
