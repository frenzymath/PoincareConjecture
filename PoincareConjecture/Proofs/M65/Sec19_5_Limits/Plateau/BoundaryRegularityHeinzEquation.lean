import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTransverse
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHeinzChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityConformalChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

private theorem straight_second_chain
    {H : LoopPlane → LoopAmbient} {E : LoopAmbient → LoopAmbient}
    {U : Set LoopPlane} {W : Set LoopAmbient}
    (hU : IsOpen U) (hW : IsOpen W) (hH : ContDiffOn ℝ ∞ H U)
    (hE : ContDiffOn ℝ ∞ E W) (hmap : MapsTo H U W)
    {z : LoopPlane} (hz : z ∈ U) (u v : LoopPlane) :
    fderiv ℝ (fderiv ℝ (E ∘ H)) z u v =
      fderiv ℝ (fderiv ℝ E) (H z) (fderiv ℝ H z u) (fderiv ℝ H z v) +
        fderiv ℝ E (H z) (fderiv ℝ (fderiv ℝ H) z u v) := by
  have hHd := (hH.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hHD : DifferentiableAt ℝ (fderiv ℝ H) z :=
    ((hH.fderiv_of_isOpen (m := ∞) hU (by simp)).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hED : DifferentiableAt ℝ (fderiv ℝ E) (H z) :=
    ((hE.fderiv_of_isOpen (m := ∞) hW (by simp)).contDiffAt
      (hW.mem_nhds (hmap hz))).differentiableAt (by simp)
  have hnear : fderiv ℝ (E ∘ H) =ᶠ[𝓝 z]
      fun w => (fderiv ℝ E (H w)).comp (fderiv ℝ H w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact fderiv_comp w ((hE.contDiffAt (hW.mem_nhds (hmap hw))).differentiableAt (by simp))
      ((hH.contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp))
  have hEDH : DifferentiableAt ℝ (fun w => fderiv ℝ E (H w)) z := hED.comp z hHd
  rw [hnear.fderiv_eq, fderiv_clm_comp hEDH hHD]
  have hchain : fderiv ℝ (fun w => fderiv ℝ E (H w)) z =
      (fderiv ℝ (fderiv ℝ E) (H z)).comp (fderiv ℝ H z) :=
    (hED.hasFDerivAt.comp z hHd.hasFDerivAt).fderiv
  simp only [hchain, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

private theorem straight_inverse_derivative
    (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
    (hE : ContDiffOn ℝ ∞ E E.source) (hEs : ContDiffOn ℝ ∞ E.symm E.target)
    {y : LoopAmbient} (hy : y ∈ E.source) (v : LoopAmbient) :
    fderiv ℝ E.symm (E y) (fderiv ℝ E y v) = v := by
  have heq : (E.symm ∘ E) =ᶠ[𝓝 y] id := by
    filter_upwards [E.open_source.mem_nhds hy] with x hx
    exact E.left_inv hx
  have hd := ((hEs.contDiffAt (E.open_target.mem_nhds (E.map_source hy))).differentiableAt
    (by simp)).hasFDerivAt.comp y
      ((hE.contDiffAt (E.open_source.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hh := congrArg (fun A : LoopAmbient →L[ℝ] LoopAmbient => A v) hd.fderiv
  rw [heq.fderiv_eq, fderiv_id] at hh
  exact hh.symm

private theorem straight_metric_compact_bounds
    (g : RiemannianMetric 3 LoopAmbient)
    (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
    (hE : ContDiffOn ℝ ∞ E E.source) (hEs : ContDiffOn ℝ ∞ E.symm E.target)
    {K : Set LoopAmbient} (hK : IsCompact K) (hKS : K ⊆ E.source) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 ≤ upper ∧
      ∀ y ∈ K, ∀ v : LoopAmbient,
        lower * ‖v‖ ^ 2 ≤ g.pullbackCoefficients E.symm (E y) v v ∧
          g.pullbackCoefficients E.symm (E y) v v ≤ upper * ‖v‖ ^ 2 := by
  let G := fun y => g.pullbackCoefficients E.symm (E y)
  have hG : ContinuousOn G K := by
    have hcoeff : ContinuousOn (g.pullbackCoefficients E.symm) E.target := by
      intro y hy
      exact (g.contDiffAt_pullbackCoefficients
        (hEs.contDiffAt (E.open_target.mem_nhds hy)).contMDiffAt).continuousAt.continuousWithinAt
    exact hcoeff.comp (hE.continuousOn.mono hKS) (fun y hy => E.map_source (hKS hy))
  have hpos (y : LoopAmbient) (hy : y ∈ K) (v : LoopAmbient) (hv : v ≠ 0) :
      0 < G y v v := by
    change 0 < g.inner (E.symm (E y))
      (mfderiv (𝓡 3) (𝓡 3) E.symm (E y) v) (mfderiv (𝓡 3) (𝓡 3) E.symm (E y) v)
    apply g.pos
    rw [mfderiv_eq_fderiv]
    intro hz
    have hh := straight_inverse_derivative E.symm hEs hE (E.map_source (hKS hy)) v
    have hz' : fderiv ℝ E.symm (E y) v = 0 := by simpa +instances only using! hz
    have hh' : fderiv ℝ E y (fderiv ℝ E.symm (E y) v) = v := by
      simpa +instances only [OpenPartialHomeomorph.symm_symm, E.left_inv (hKS hy)] using! hh
    rw [hz', map_zero] at hh'
    exact hv hh'.symm
  let S := K ×ˢ sphere (0 : LoopAmbient) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hfun : ContinuousOn (fun z : LoopAmbient × LoopAmbient => G z.1 z.2 z.2) S :=
    (((hG.comp continuousOn_fst (fun _ hz => hz.1)).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd)
  have hpositive (z : LoopAmbient × LoopAmbient) (hz : z ∈ S) : 0 < G z.1 z.2 z.2 := by
    apply hpos z.1 hz.1 z.2
    intro heq
    have hn := mem_sphere_zero_iff_norm.mp hz.2
    rw [heq, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨lower, hlower, hlo⟩ := hS.exists_forall_le' hfun hpositive
  obtain ⟨upper, hhi⟩ := hS.exists_bound_of_continuousOn hfun
  refine ⟨lower, max upper 0, hlower, le_max_right _ _, ?_⟩
  intro y hy v
  by_cases hv : v = 0
  · simp [hv]
  let w : LoopAmbient := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
  have hrep : ‖v‖ • w = v := by
    simp only [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hwS : (y, w) ∈ S := ⟨hy, mem_sphere_zero_iff_norm.mpr hw⟩
  have heq : G y v v = ‖v‖ ^ 2 * G y w w := by
    calc
      _ = G y (‖v‖ • w) (‖v‖ • w) := by rw [hrep]
      _ = _ := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
  change lower * ‖v‖ ^ 2 ≤ G y v v ∧ G y v v ≤ max upper 0 * ‖v‖ ^ 2
  rw [heq]
  constructor
  · simpa only [mul_comm lower] using mul_le_mul_of_nonneg_left (hlo _ hwS) (sq_nonneg ‖v‖)
  · rw [mul_comm (max upper 0)]
    exact mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans ((hhi _ hwS).trans (le_max_left _ _))) (sq_nonneg ‖v‖)

theorem straight_harmonic_equation
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H : LoopPlane → LoopAmbient} {U : Set LoopPlane} (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U)
    (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
    (hE : ContDiffOn ℝ ∞ E E.source) (hmap : MapsTo H U E.source)
    (heq : ∀ z ∈ U, (∑ i : Fin 2, fderiv ℝ (fderiv ℝ H) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
      ∑ i : Fin 2, M65Gauss.connectionCoefficient D (H z)
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0)
    {z : LoopPlane} (hz : z ∈ U) :
    (∑ i : Fin 2, fderiv ℝ (fderiv ℝ (E ∘ H)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      ∑ i : Fin 2,
        (fderiv ℝ (fderiv ℝ E) (H z)
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i)) -
        fderiv ℝ E (H z) (M65Gauss.connectionCoefficient D (H z)
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i)))) := by
  simp_rw [straight_second_chain hU E.open_source hH hE hmap hz]
  rw [Finset.sum_add_distrib, ← map_sum, eq_neg_of_add_eq_zero_left (heq z hz), map_neg,
    Finset.sum_sub_distrib, map_sum, sub_eq_add_neg]

set_option maxHeartbeats 1800000 in

theorem straight_harmonic_transverse_growth
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H : LoopPlane → LoopAmbient} {U : Set LoopPlane} {K : Set LoopAmbient}
    (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U)
    (hK : IsCompact K) (hHK : MapsTo H U K)
    (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
    (hE : ContDiffOn ℝ ∞ E E.source) (hEs : ContDiffOn ℝ ∞ E.symm E.target)
    (hKS : K ⊆ E.source) (j : Fin 3)
    (heq : ∀ z ∈ U, (∑ i : Fin 2, fderiv ℝ (fderiv ℝ H) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
      ∑ i : Fin 2, M65Gauss.connectionCoefficient D (H z)
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0)
    (hdiag : ∀ z ∈ U,
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
    (hmixed : ∀ z ∈ U,
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U,
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (E ∘ H)) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
        C * ∑ k : Fin 3, if k = j then 0 else
          ∑ i : Fin 2, (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ i) k) ^ 2 := by
  classical
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hE1 := hE.fderiv_of_isOpen (m := ∞) E.open_source (by simp)
  have hE2 := hE1.fderiv_of_isOpen (m := ∞) E.open_source (by simp)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn (hE1.continuousOn.mono hKS)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn (hE2.continuousOn.mono hKS)
  obtain ⟨BG, hBG, hGB⟩ := M65Euler.connection_quadratic_bound D hK
  have hAcont : ContinuousOn (fun y => fderiv ℝ E.symm (E y)) K :=
    (hEs.fderiv_of_isOpen (m := ∞) E.open_target (by simp)).continuousOn.comp
      (hE.continuousOn.mono hKS) (fun y hy => E.map_source (hKS hy))
  obtain ⟨BA, hBA⟩ := hK.exists_bound_of_continuousOn hAcont
  obtain ⟨lower, upper, hlower, hupper, hmetric⟩ := straight_metric_compact_bounds g E hE hEs hK hKS
  let Q := max B2 0 + max B1 0 * BG
  let A := max BA 0
  let T := 2 * upper / lower
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hA : 0 ≤ A := le_max_right _ _
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  refine ⟨Q * A ^ 2 * T, by positivity, ?_⟩
  intro z hz
  let v := fun i : Fin 2 => fderiv ℝ H z (b i)
  let w := fun i : Fin 2 => fderiv ℝ (E ∘ H) z (b i)
  have hy : H z ∈ K := hHK hz
  have hs : H z ∈ E.source := hKS hy
  have hHd := (hH.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hEd := (hE.contDiffAt (E.open_source.mem_nhds hs)).differentiableAt (by simp)
  have hw (i : Fin 2) : w i = fderiv ℝ E (H z) (v i) := by
    dsimp only [w, v]
    rw [fderiv_comp z hEd hHd, ContinuousLinearMap.comp_apply]
  have hback (i : Fin 2) : fderiv ℝ E.symm (E (H z)) (w i) = v i := by
    rw [hw]
    exact straight_inverse_derivative E hE hEs hs (v i)
  let G := g.pullbackCoefficients E.symm (E (H z))
  have hG (a c : LoopAmbient) : G a c = g.inner (H z)
      (fderiv ℝ E.symm (E (H z)) a) (fderiv ℝ E.symm (E (H z)) c) := by
    simp +instances only [G, RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply, mfderiv_eq_fderiv]
    convert! congrArg (fun y : LoopAmbient => g.euclideanCoefficients y
      (fderiv ℝ E.symm (E (H z)) a) (fderiv ℝ E.symm (E (H z)) c)) (E.left_inv hs) using 1
  have hcols (i k : Fin 2) : G (w i) (w k) = g.inner (H z) (v i) (v k) := by
    rw [hG, hback, hback]
  have htrans : ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 ≤ T *
      ∑ k : Fin 3, if k = j then 0 else w 0 k ^ 2 + w 1 k ^ 2 :=
    m65Boundary_transverse_derivative_bound_axis G
      (fun a c => by rw [hG, hG]; exact g.symm _ _ _) hlower hupper
      (fun a => (hmetric _ hy a).1) (fun a => (hmetric _ hy a).2) j (w 0) (w 1)
      (by rw [hcols, hcols]; exact hdiag z hz) (by rw [hcols]; exact hmixed z hz)
  have hcolbound (i : Fin 2) : ‖v i‖ ≤ A * ‖w i‖ := by
    rw [← hback i]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((hBA _ hy).trans (le_max_left _ _)) (norm_nonneg _))
  have hsum : ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 ≤ A ^ 2 * (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2) := by
    have h0 := pow_le_pow_left₀ (norm_nonneg (v 0)) (hcolbound 0) 2
    have h1 := pow_le_pow_left₀ (norm_nonneg (v 1)) (hcolbound 1) 2
    rw [mul_pow] at h0 h1
    nlinarith
  have hterm (i : Fin 2) :
      ‖fderiv ℝ (fderiv ℝ E) (H z) (v i) (v i) -
        fderiv ℝ E (H z) (M65Gauss.connectionCoefficient D (H z) (v i) (v i))‖ ≤
          Q * ‖v i‖ ^ 2 := by
    have hsecond : ‖fderiv ℝ (fderiv ℝ E) (H z) (v i) (v i)‖ ≤ max B2 0 * ‖v i‖ ^ 2 := by
      calc
        _ ≤ ‖fderiv ℝ (fderiv ℝ E) (H z)‖ * ‖v i‖ * ‖v i‖ :=
          (fderiv ℝ (fderiv ℝ E) (H z)).le_opNorm₂ _ _
        _ ≤ max B2 0 * ‖v i‖ * ‖v i‖ := by gcongr; exact (hB2 _ hy).trans (le_max_left _ _)
        _ = _ := by ring
    have hfirst : ‖fderiv ℝ E (H z) (M65Gauss.connectionCoefficient D (H z) (v i) (v i))‖ ≤
        max B1 0 * (BG * ‖v i‖ ^ 2) :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul ((hB1 _ hy).trans (le_max_left _ _)) (hGB _ hy _)
          (norm_nonneg _) (le_max_right _ _))
    exact (norm_sub_le _ _).trans (by dsimp only [Q]; nlinarith)
  have hlap : ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (E ∘ H)) z (b i) (b i)‖ ≤
      Q * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
    rw [straight_harmonic_equation D hU hH E hE (fun x hx => hKS (hHK hx)) heq hz]
    calc
      _ ≤ ∑ i : Fin 2, ‖fderiv ℝ (fderiv ℝ E) (H z) (v i) (v i) -
          fderiv ℝ E (H z) (M65Gauss.connectionCoefficient D (H z) (v i) (v i))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 2, Q * ‖v i‖ ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by rw [Fin.sum_univ_two]; ring
  change ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (E ∘ H)) z (b i) (b i)‖ ≤
    Q * A ^ 2 * T * ∑ k : Fin 3, if k = j then 0 else ∑ i : Fin 2, w i k ^ 2
  have hright : (∑ k : Fin 3, if k = j then 0 else ∑ i : Fin 2, w i k ^ 2) =
      ∑ k : Fin 3, if k = j then 0 else w 0 k ^ 2 + w 1 k ^ 2 := by
    simp only [Fin.sum_univ_two]
  rw [hright]
  calc
    _ ≤ Q * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := hlap
    _ ≤ Q * (A ^ 2 * (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2)) := mul_le_mul_of_nonneg_left hsum hQ
    _ ≤ Q * (A ^ 2 * (T * ∑ k : Fin 3, if k = j then 0 else w 0 k ^ 2 + w 1 k ^ 2)) := by
      gcongr
    _ = _ := by ring

private theorem plane_complex_second (H : LoopPlane → LoopAmbient)
    (z u v : ℂ) :
    fderiv ℝ (fderiv ℝ (H ∘ Complex.orthonormalBasisOneI.repr)) z u v =
      fderiv ℝ (fderiv ℝ H) (Complex.orthonormalBasisOneI.repr z)
        (Complex.orthonormalBasisOneI.repr u) (Complex.orthonormalBasisOneI.repr v) := by
  let e := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have h := e.iteratedFDerivWithin_comp_right H uniqueDiffOn_univ (mem_univ (e z)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hh := congrArg (fun T => T ![u, v]) h
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, Matrix.cons_val_zero,
    Matrix.cons_val_one, e, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hh

theorem plane_harmonic_of_complex_equation
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H : LoopPlane → LoopAmbient} {z : ℂ}
    (hH : ContDiffAt ℝ ∞ H (Complex.orthonormalBasisOneI.repr z))
    (heq : M65Branch.dbar (M65Branch.complexGradient (H ∘ Complex.orthonormalBasisOneI.repr)) z =
      M65Branch.harmonicMatrix D (H ∘ Complex.orthonormalBasisOneI.repr) z
        (M65Branch.complexGradient (H ∘ Complex.orthonormalBasisOneI.repr) z)) :
    (∑ i : Fin 2, fderiv ℝ (fderiv ℝ H) (Complex.orthonormalBasisOneI.repr z)
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
      ∑ i : Fin 2, M65Gauss.connectionCoefficient D (H (Complex.orthonormalBasisOneI.repr z))
        (fderiv ℝ H (Complex.orthonormalBasisOneI.repr z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ H (Complex.orthonormalBasisOneI.repr z)
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
  let e := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have hHs : ContDiffAt ℝ ∞ (H ∘ Complex.orthonormalBasisOneI.repr) z :=
    hH.comp z e.contDiff.contDiffAt
  have hcol (v : ℂ) : fderiv ℝ (H ∘ Complex.orthonormalBasisOneI.repr) z v =
      fderiv ℝ H (e z) (e v) :=
    congrArg (fun L : ℂ →L[ℝ] LoopAmbient => L v)
      (((hH.differentiableAt (by simp)).hasFDerivAt.comp z e.hasFDerivAt).fderiv)
  have he1 : e 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i; fin_cases i <;>
      simp [e, Complex.orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have heI : e Complex.I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i; fin_cases i <;>
      simp [e, Complex.orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  rw [M65Branch.dbar_complexGradient hHs, M65Branch.harmonicMatrix_apply_gradient] at heq
  have hh := congrArg (fun v : Fin 3 → ℂ => (2 : ℂ) • v) heq
  simp only [smul_smul, mul_neg, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul, neg_one_smul] at hh
  simp only [plane_complex_second, hcol] at hh
  change M65Branch.coordinateComplexification
    (fderiv ℝ (fderiv ℝ H) (e z) (e 1) (e 1) +
      fderiv ℝ (fderiv ℝ H) (e z) (e Complex.I) (e Complex.I)) =
    -M65Branch.coordinateComplexification
      (M65Gauss.connectionCoefficient D (H (e z))
        (fderiv ℝ H (e z) (e 1)) (fderiv ℝ H (e z) (e 1)) +
        M65Gauss.connectionCoefficient D (H (e z))
          (fderiv ℝ H (e z) (e Complex.I)) (fderiv ℝ H (e z) (e Complex.I))) at hh
  rw [he1, heI] at hh
  ext k
  have hk := congrArg (fun v : Fin 3 → ℂ => (v k).re) hh
  simp only [M65Branch.coordinateComplexification, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, PiLp.proj_apply,
    Pi.neg_apply, Complex.neg_re, Complex.ofReal_re, PiLp.add_apply] at hk
  simpa only [Fin.sum_univ_two, PiLp.add_apply, PiLp.zero_apply, e,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using add_eq_zero_iff_eq_neg.mpr hk

theorem plane_conformal_of_complex_norm
    (g : RiemannianMetric 3 LoopAmbient) {H : LoopPlane → LoopAmbient} {z : ℂ} {a : ℝ}
    (hH : DifferentiableAt ℝ H (Complex.orthonormalBasisOneI.repr z))
    (hconf : ∀ v : ℂ,
      g.inner (H (Complex.orthonormalBasisOneI.repr z))
        (fderiv ℝ (H ∘ Complex.orthonormalBasisOneI.repr) z v)
        (fderiv ℝ (H ∘ Complex.orthonormalBasisOneI.repr) z v) = a * ‖v‖ ^ 2) :
    let x := Complex.orthonormalBasisOneI.repr z
    let v := fderiv ℝ H x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    let w := fderiv ℝ H x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    g.inner (H x) v v = g.inner (H x) w w ∧ g.inner (H x) v w = 0 := by
  let e := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let v := fderiv ℝ H (e z) (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let w := fderiv ℝ H (e z) (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hcol (b : ℂ) : fderiv ℝ (H ∘ Complex.orthonormalBasisOneI.repr) z b =
      fderiv ℝ H (e z) (e b) :=
    congrArg (fun L : ℂ →L[ℝ] LoopAmbient => L b) (hH.hasFDerivAt.comp z e.hasFDerivAt).fderiv
  have he1 : e 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i; fin_cases i <;>
      simp [e, Complex.orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have heI : e Complex.I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i; fin_cases i <;>
      simp [e, Complex.orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have hv : g.inner (H (e z)) v v = a := by
    simpa +instances only [hcol, he1, norm_one, one_pow, mul_one] using! hconf 1
  have hw : g.inner (H (e z)) w w = a := by
    simpa +instances only [hcol, heI, Complex.norm_I, one_pow, mul_one] using! hconf Complex.I
  have hsum := hconf (1 + Complex.I)
  rw [hcol, map_add, he1, heI, map_add] at hsum
  have hnorm : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply]
  rw [hnorm] at hsum
  change g.inner (H (e z)) (v + w) (v + w) = a * 2 at hsum
  simp only [map_add, add_apply] at hsum
  have hsym := g.symm (H (e z)) w v
  change g.inner (H (e z)) v v = g.inner (H (e z)) w w ∧ g.inner (H (e z)) v w = 0
  exact ⟨hv.trans hw.symm, by linarith⟩

theorem straight_metric_data (g : RiemannianMetric 3 LoopAmbient)
    {H : LoopPlane → LoopAmbient} {U K : Set LoopPlane}
    (hU : IsOpen U) (hUK : U ⊆ K) (hK : IsCompact K)
    (hHc : ContinuousOn H K) (hH : ContDiffOn ℝ ∞ H U)
    (E : OpenPartialHomeomorph LoopAmbient LoopAmbient)
    (hE : ContDiffOn ℝ ∞ E E.source) (hEs : ContDiffOn ℝ ∞ E.symm E.target)
    (hsource : MapsTo H K E.source)
    (hdiag : ∀ z ∈ U,
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
    (hmixed : ∀ z ∈ U,
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = 0) :
    let G := fun z => g.pullbackCoefficients E.symm (E (H z))
    ContinuousOn G K ∧
      (∀ z ∈ K, ∀ v w, G z v w = G z w v) ∧
      (∀ z ∈ K, ∀ v : LoopAmbient, v ≠ 0 → 0 < G z v v) ∧
      (∀ z ∈ U,
        G z (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
        G z (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ 1))) ∧
      (∀ z ∈ U,
        G z (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = 0) := by
  let G := fun z => g.pullbackCoefficients E.symm (E (H z))
  have hcoeff : ContinuousOn (g.pullbackCoefficients E.symm) E.target := by
    intro y hy
    exact (g.contDiffAt_pullbackCoefficients
      (hEs.contDiffAt (E.open_target.mem_nhds hy)).contMDiffAt).continuousAt.continuousWithinAt
  have hc : ContinuousOn G K := hcoeff.comp (hE.continuousOn.comp hHc hsource)
    (fun z hz => E.map_source (hsource hz))
  obtain ⟨lower, _upper, hlower, _hupper, hbound⟩ :=
    straight_metric_compact_bounds g E hE hEs (hK.image_of_continuousOn hHc)
      (by rintro _ ⟨z, hz, rfl⟩; exact hsource hz)
  have hG (z : LoopPlane) (hz : z ∈ K) (v w : LoopAmbient) :
      G z v w = g.inner (H z) (fderiv ℝ E.symm (E (H z)) v)
        (fderiv ℝ E.symm (E (H z)) w) := by
    simp +instances only [G, RiemannianMetric.pullbackCoefficients,
      ContinuousLinearMap.bilinearComp_apply, mfderiv_eq_fderiv]
    convert! congrArg (fun y : LoopAmbient => g.euclideanCoefficients y
      (fderiv ℝ E.symm (E (H z)) v) (fderiv ℝ E.symm (E (H z)) w))
        (E.left_inv (hsource hz)) using 1
  have hcols (z : LoopPlane) (hz : z ∈ U) (i k : Fin 2) :
      G z (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ (E ∘ H) z (EuclideanSpace.basisFun (Fin 2) ℝ k)) =
      g.inner (H z) (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ H z (EuclideanSpace.basisFun (Fin 2) ℝ k)) := by
    have hs := hsource (hUK hz)
    rw [hG z (hUK hz), fderiv_comp z
      ((hE.contDiffAt (E.open_source.mem_nhds hs)).differentiableAt (by simp))
      ((hH.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    simp only [ContinuousLinearMap.comp_apply, straight_inverse_derivative E hE hEs hs]
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · intro z hz v w
    rw [hG z hz, hG z hz]
    exact g.symm _ _ _
  · intro z hz v hv
    exact (mul_pos hlower (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le
      (hbound (H z) (mem_image_of_mem H hz) v).1
  · intro z hz
    rw [hcols z hz, hcols z hz]
    exact hdiag z hz
  · intro z hz
    rw [hcols z hz]
    exact hmixed z hz

end PoincareConjecture.M65Boundary
