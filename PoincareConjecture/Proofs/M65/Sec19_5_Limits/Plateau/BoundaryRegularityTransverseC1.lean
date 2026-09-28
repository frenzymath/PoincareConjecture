import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityReflectedEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityLocalC1
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerClassical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M65Boundary

private theorem classical_laplacian_weak {N : ℕ} {U : Set LoopPlane}
    (hU : IsOpen U)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) U)
    (hX : ContDiffOn ℝ ∞ X.value U)
    (hD : ∀ i, MemLp (X.derivative i) 2 (volume.restrict U)) {C : ℝ}
    (hgrowth : ∀ z ∈ U,
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2) :
    let f := fun k z => (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) k
    (∀ k, IntegrableOn (f k) U) ∧
      (∀ k, ∀ᵐ z ∂volume.restrict U,
        |f k z| ≤ C * ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ∧
      ∀ k (test : 𝓢(LoopPlane, ℝ)), HasCompactSupport test → tsupport test ⊆ U →
        (∫ z in U, ∑ i : Fin 2, X.derivative i z k *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
            -(∫ z in U, f k z * test z) := by
  classical
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let f := fun k z => (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) k
  have hX1 : ContDiffOn ℝ 1 (id ∘ X.value) U := hX.of_le (by simp)
  have hcol (i : Fin 2) : (fun z => fderiv ℝ X.value z (b i))
      =ᵐ[volume.restrict U] X.derivative i :=
    M65Euler.classical_derivative_eq_weak hU X X.value hX1 (ae_of_all _ fun _ => rfl) i
  have hsumI : IntegrableOn (fun z => ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) U :=
    integrable_finsetSum _ (fun i _ => (hD i).norm.integrable_sq)
  have hfc (k : Fin N) : ContinuousOn (f k) U := by
    have h2 := (hX.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen
      (m := ∞) hU (by simp)
    change ContinuousOn ((EuclideanSpace.proj (𝕜 := ℝ) k) ∘
      fun z => ∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) U
    apply (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp_continuousOn
    apply continuousOn_finsetSum
    intro i _
    exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hfg (k : Fin N) : ∀ᵐ z ∂volume.restrict U,
      |f k z| ≤ C * ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2 := by
    filter_upwards [ae_all_iff.mpr hcol, ae_restrict_mem hU.measurableSet] with z hd hz
    have hp := PiLp.norm_apply_le
      (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) k
    rw [Real.norm_eq_abs] at hp
    exact hp.trans (by simpa only [b, hd] using hgrowth z hz)
  refine ⟨(fun k => (hsumI.const_mul C).mono'
    ((hfc k).aestronglyMeasurable hU.measurableSet)
      (by simpa only [Real.norm_eq_abs] using hfg k)), hfg, ?_⟩
  intro k test hc hs
  let row := fun i z => (fderiv ℝ X.value z (b i)) k
  have hrow (i : Fin 2) : ContDiffOn ℝ 1 (row i) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn
      ((hX.fderiv_of_isOpen (m := 1) hU (by decide)).clm_apply contDiffOn_const)
  have hdrow (i : Fin 2) (z : LoopPlane) (hz : z ∈ U) :
      fderiv ℝ (row i) z (b i) = (fderiv ℝ (fderiv ℝ X.value) z (b i) (b i)) k := by
    have hDf : DifferentiableAt ℝ (fderiv ℝ X.value) z :=
      ((hX.fderiv_of_isOpen (m := 1) hU (by decide)).contDiffAt
        (hU.mem_nhds hz)).differentiableAt
        one_ne_zero
    have hd := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp z
      (hDf.clm_apply (differentiableAt_const (b i))).hasFDerivAt
    have hh := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (b i)) hd.fderiv
    change fderiv ℝ (row i) z (b i) =
      (fderiv ℝ (fun z => fderiv ℝ X.value z (b i)) z (b i)) k at hh
    rw [fderiv_clm_apply hDf (differentiableAt_const (b i))] at hh
    simpa only [ContinuousLinearMap.comp_apply, fderiv_fun_const, Pi.zero_apply, zero_apply,
      map_zero, add_apply, zero_add, ContinuousLinearMap.flip_apply] using hh
  have hi (i : Fin 2) := M65Euler.classical_scalar_weak_identity hU (hrow i) test hc hs (b i)
  have hweak : (∫ z in U, ∑ i : Fin 2, row i z * fderiv ℝ test z (b i)) =
      -(∫ z in U, f k z * test z) := by
    rw [integral_finsetSum _ (fun i _ => (hi i).2.1)]
    have hfrow : (fun z => f k z * test z) =ᵐ[volume.restrict U]
        fun z => ∑ i : Fin 2, fderiv ℝ (row i) z (b i) * test z := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      simp only [hdrow _ z hz, f, Fin.sum_univ_two, PiLp.add_apply, add_mul]
    rw [integral_congr_ae hfrow, integral_finsetSum _ (fun i _ => (hi i).1)]
    simp_rw [(hi _).2.2]
    rw [Finset.sum_neg_distrib, neg_neg]
  calc
    _ = ∫ z in U, ∑ i : Fin 2, row i z * fderiv ℝ test z (b i) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hcol] with z hz
      simp only [row, hz, b]
    _ = _ := hweak

private theorem odd_energy_decay {N : ℕ} {R beta Λ : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R))
    (Y : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) (R / 4)))
    (hY : ∀ i z, Y.derivative i z = if 0 ≤ z 1 then X.derivative i z else
      (if i = 0 then (-1 : ℝ) else 1) • X.derivative i (boundaryPlaneReflection z))
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * beta)) :
    ∀ x ∈ ball (0 : LoopPlane) (R / 16), ∀ r : ℝ, 0 < r → r ≤ R / 32 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) ≤
        (2 * Λ) * r ^ (2 * beta) := by
  classical
  let f := fun z => ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2
  let K := closedBall (0 : LoopPlane) (R / 2)
  have hKX : K ⊆ ball (0 : LoopPlane) R := closedBall_subset_ball (by linarith)
  have hf : IntegrableOn f K := integrable_finsetSum _ fun i _ =>
    (X.derivative_memLp i K (isCompact_closedBall _ _) hKX).norm.integrable_sq
  have hpre : boundaryPlaneReflection ⁻¹' K = K := by
    ext z
    simp only [K, mem_preimage, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
  have hfr : IntegrableOn (fun z => f (boundaryPlaneReflection z)) K := by
    have hh := (boundaryPlaneReflection.measurePreserving.restrict_preimage_emb
      boundaryPlaneReflection.toHomeomorph.measurableEmbedding K).integrable_comp_of_integrable hf
    change Integrable (fun z => f (boundaryPlaneReflection z)) (volume.restrict K)
    simpa only [hpre, Function.comp_def] using hh
  intro x hx r hr hrr
  have hxn : ‖x‖ < R / 16 := mem_ball_zero_iff.mp hx
  have hball : closedBall x r ⊆ ball (0 : LoopPlane) (R / 4) := by
    apply closedBall_subset_ball'
    rw [dist_zero_right]
    linarith
  have hballK : closedBall x r ⊆ K := hball.trans
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hYI : IntegrableOn (fun z => ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2)
      (closedBall x r) := integrable_finsetSum _ fun i _ =>
    (Y.derivative_memLp i _ (isCompact_closedBall _ _) hball).norm.integrable_sq
  have hpoint (z : LoopPlane) :
      (∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) ≤ f z + f (boundaryPlaneReflection z) := by
    have hf0 (w : LoopPlane) : 0 ≤ f w := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_cases hz : 0 ≤ z 1
    · simpa only [hY, if_pos hz] using le_add_of_nonneg_right (hf0 (boundaryPlaneReflection z))
    · have he : (∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) = f (boundaryPlaneReflection z) := by
        simp only [hY, if_neg hz, Fin.sum_univ_two, f]
        norm_num
      rw [he]
      exact le_add_of_nonneg_left (hf0 z)
  have hpreball : boundaryPlaneReflection ⁻¹' closedBall (boundaryPlaneReflection x) r =
      closedBall x r := by
    ext z
    simp only [mem_preimage, mem_closedBall, LinearIsometryEquiv.dist_map]
  have hchange : (∫ z in closedBall x r, f (boundaryPlaneReflection z)) =
      ∫ z in closedBall (boundaryPlaneReflection x) r, f z := by
    have hh := boundaryPlaneReflection.measurePreserving.setIntegral_preimage_emb
      boundaryPlaneReflection.toHomeomorph.measurableEmbedding f
        (closedBall (boundaryPlaneReflection x) r)
    simpa only [hpreball] using hh
  have hxc : x ∈ closedBall (0 : LoopPlane) (R / 4) :=
    mem_closedBall_zero_iff.mpr (by linarith)
  have hxr : boundaryPlaneReflection x ∈ closedBall (0 : LoopPlane) (R / 4) := by
    simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hxc
  calc
    _ ≤ ∫ z in closedBall x r, f z + f (boundaryPlaneReflection z) :=
      setIntegral_mono_on hYI ((hf.mono_set hballK).add (hfr.mono_set hballK))
        measurableSet_closedBall (fun z _ => hpoint z)
    _ = (∫ z in closedBall x r, f z) +
        ∫ z in closedBall (boundaryPlaneReflection x) r, f z := by
      rw [integral_add (hf.mono_set hballK) (hfr.mono_set hballK), hchange]
    _ ≤ Λ * r ^ (2 * beta) + Λ * r ^ (2 * beta) :=
      add_le_add (hdecay x hxc r hr (by linarith))
        (hdecay _ hxr r hr (by linarith))
    _ = _ := by ring

set_option maxHeartbeats 1800000 in

theorem zero_trace_quadratic_contDiffOn {N : ℕ} {R C H beta Λ : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R))
    (hX : ContDiffOn ℝ ∞ X.value (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hXc : ContinuousOn X.value (closedBall (0 : LoopPlane) (R / 2)))
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hb : 0 < beta) (hΛ : 0 ≤ Λ)
    (hholder : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2),
      ∀ z ∈ closedBall (0 : LoopPlane) (R / 2),
      ‖X.value z - X.value x‖ ≤ H * dist z x ^ beta)
    (hzero : ∀ z ∈ closedBall (0 : LoopPlane) (R / 2), z 1 = 0 → X.value z = 0)
    (hgrowth : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1},
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ X.value z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2)
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        Λ * r ^ (2 * beta)) :
    ContDiffOn ℝ 1 X.value (closedBall (0 : LoopPlane) (R / 64) ∩ {z | 0 ≤ z 1}) := by
  classical
  let U := ball (0 : LoopPlane) (R / 4) ∩ {z | 0 < z 1}
  let K := closedBall (0 : LoopPlane) (R / 4) ∩ {z | 0 ≤ z 1}
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hKU : K ⊆ ball (0 : LoopPlane) R := fun z hz =>
    closedBall_subset_ball (by linarith) hz.1
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  have hUK : U ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hKhalf : K ⊆ closedBall (0 : LoopPlane) (R / 2) := fun z hz =>
    closedBall_subset_closedBall (by linarith) hz.1
  have hUfull : U ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1} := fun z hz =>
    ⟨ball_subset_ball (by linarith) hz.1, hz.2⟩
  let A := M65Euler.restrict_map X (hUK.trans hKU)
  have hD (i : Fin 2) : MemLp (A.derivative i) 2 (volume.restrict U) :=
    (X.derivative_memLp i K hK hKU).mono_measure (Measure.restrict_mono_set volume hUK)
  obtain ⟨Y, hYv, hYD, hYc, hYholder⟩ := halfDisk_odd_localMap
    (show 0 < R / 4 by positivity) A X.value (ae_of_all _ fun _ => rfl)
    (X.value_memLp K hK hKU) (fun i => X.derivative_memLp i K hK hKU) hb hH
    (hXc.mono hKhalf) (fun x hx z hz => hholder x (hKhalf hx) z (hKhalf hz))
    (fun z hz he => hzero z (hKhalf hz) he)
  let f := fun k z => (∑ i : Fin 2, fderiv ℝ (fderiv ℝ X.value) z
    (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) k
  obtain ⟨hf, hfg, hfeq⟩ := classical_laplacian_weak hU A (hX.mono hUfull) hD
    (fun z hz => hgrowth z (hUfull hz))
  have hDI (i : Fin 2) : IntegrableOn (A.derivative i) U := by
    have : IsFiniteMeasure (volume.restrict U) :=
      isFiniteMeasure_restrict.mpr ((measure_mono hUK).trans_lt hK.measure_lt_top).ne
    exact (hD i).integrable (by norm_num)
  obtain ⟨hgI, hgeq⟩ := halfDisk_odd_localMap_equation A.derivative Y hYD hDI f hf hfeq
  have hnorm (D : Fin 2 → EuclideanSpace ℝ (Fin N)) :
      (∑ k : Fin N, ∑ i : Fin 2, D i k ^ 2) = ∑ i : Fin 2, ‖D i‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp only [EuclideanSpace.real_norm_sq_eq]
  have hgrowth' := halfDisk_odd_localMap_growth A.derivative Y hYD f (fun k => by
    simpa only [hnorm, f, U, A, M65Euler.restrict_map] using hfg k)
  have hYdecay := odd_energy_decay hR X Y hYD hdecay
  have hradius : 8 * (R / 32) = R / 4 := by ring
  let Z : M65LocalWeakMap
      (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) (8 * (R / 32))) := {
    value := Y.value
    derivative := Y.derivative
    value_memLp := by simpa only [hradius] using Y.value_memLp
    derivative_memLp := by simpa only [hradius] using Y.derivative_memLp
    weak_derivative := by simpa only [hradius] using Y.weak_derivative }
  have hregular : ContDiffOn ℝ 1 Y.value (ball (0 : LoopPlane) (R / 32)) := by
    apply local_quadratic_contDiffOn 0 (show 0 < R / 32 by positivity) Z
      (f := fun k z => if 0 ≤ z 1 then f k z else -f k (boundaryPlaneReflection z))
      (C := C) (H := 2 * H) (beta := beta) (Λ := 2 * Λ)
    · simpa only [Z, hradius] using hYc.mono ball_subset_closedBall
    · simpa only [hradius] using hgI
    · simpa only [Z, hradius] using hgeq
    · exact hC
    · positivity
    · exact hb
    · positivity
    · simpa only [Z, hradius, hnorm] using hgrowth'
    · simpa only [Z, hradius] using
        (fun x hx z hz => hYholder x (ball_subset_closedBall hx) z (ball_subset_closedBall hz))
    · simpa only [Z, show 2 * (R / 32) = R / 16 by ring] using hYdecay
  apply hregular.congr_mono
  · intro z hz
    exact (hYv z).trans (if_pos hz.2) |>.symm
  · intro z hz
    exact closedBall_subset_ball (by linarith) hz.1

end PoincareConjecture.M65Boundary
