import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.C2WeakLaplacian

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture

open M65Boundary

private theorem odd_energy_decay {N : ℕ} {R beta Lambda : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R))
    (Y : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) (R / 4)))
    (hY : ∀ i z, Y.derivative i z = if 0 ≤ z 1 then X.derivative i z else
      (if i = 0 then (-1 : ℝ) else 1) • X.derivative i (boundaryPlaneReflection z))
    (hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 4), ∀ r : ℝ, 0 < r → r ≤ R / 4 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        Lambda * r ^ (2 * beta)) :
    ∀ x ∈ ball (0 : LoopPlane) (R / 16), ∀ r : ℝ, 0 < r → r ≤ R / 32 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖Y.derivative i z‖ ^ 2) ≤
        (2 * Lambda) * r ^ (2 * beta) := by
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
    _ ≤ Lambda * r ^ (2 * beta) + Lambda * r ^ (2 * beta) :=
      add_le_add (hdecay x hxc r hr (by linarith))
        (hdecay _ hxr r hr (by linarith))
    _ = _ := by ring

theorem m64C2_zero_trace_quadratic_contDiffOn {N : ℕ} {R C H beta Lambda : ℝ} (hR : 0 < R)
    (X : M65LocalWeakMap (id : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
      (ball (0 : LoopPlane) R))
    (hX : ContDiffOn ℝ 2 X.value (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hXc : ContinuousOn X.value (closedBall (0 : LoopPlane) (R / 2)))
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hb : 0 < beta) (hLambda : 0 ≤ Lambda)
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
        Lambda * r ^ (2 * beta)) :
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
  obtain ⟨hf, hfg, hfeq⟩ := m64C2_classical_laplacian_weak hU A (hX.mono hUfull) hD
    (fun z hz => hgrowth z (hUfull hz))
  have hDI (i : Fin 2) : IntegrableOn (A.derivative i) U := by
    have : IsFiniteMeasure (volume.restrict U) :=
      isFiniteMeasure_restrict.mpr ((measure_mono hUK).trans_lt hK.measure_lt_top).ne
    exact (hD i).integrable (by norm_num)
  obtain ⟨hgI, hgeq⟩ := halfDisk_odd_localMap_equation A.derivative Y hYD hDI f hf hfeq
  have hnorm (V : Fin 2 → EuclideanSpace ℝ (Fin N)) :
      (∑ k : Fin N, ∑ i : Fin 2, V i k ^ 2) = ∑ i : Fin 2, ‖V i‖ ^ 2 := by
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
      (C := C) (H := 2 * H) (beta := beta) (Λ := 2 * Lambda)
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

end PoincareConjecture
