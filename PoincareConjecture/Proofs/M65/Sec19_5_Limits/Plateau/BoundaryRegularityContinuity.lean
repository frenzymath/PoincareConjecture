import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityFullDecay
import Mathlib.MeasureTheory.Measure.OpenPos











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65Interior





theorem weakDisk_boundary_holder_representative
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ (r β H : ℝ) (v : LoopPlane → EuclideanSpace ℝ (Fin N)),
      0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < H ∧ ContinuousOn v (closedBall 0 r) ∧
      (v =ᵐ[volume.restrict (closedBall 0 r)] fun z =>
        e (if 0 ≤ z 1 then F.value (diskBoundaryCoordinate p z)
          else F.value (diskBoundaryCoordinate p (boundaryPlaneReflection z)))) ∧
      ∀ x ∈ closedBall (0 : LoopPlane) r, ∀ y ∈ closedBall (0 : LoopPlane) r,
        ‖v y - v x‖ ≤ H * dist y x ^ β := by
  obtain ⟨Q, R, α, B, hR, hRQ, hα, hα1, hB, X, hXv, _hXd, henergy⟩ :=
    weakDisk_exists_boundary_full_energy_decay g he hinj hemb compact hγ hsmooth hregular
      F hmin hp
  obtain ⟨c, _C, hc, _hC, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  have hRU : closedBall (0 : LoopPlane) R ⊆ ball 0 Q := closedBall_subset_ball hRQ
  have hdecay : ∀ x ∈ closedBall (0 : LoopPlane) (R / 2), ∀ r : ℝ, 0 < r → r ≤ R / 2 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        ((2 / c) * B) * r ^ (2 * (α / 2)) := by
    intro x hx r hr hrR
    have hsub : closedBall x r ⊆ ball (0 : LoopPlane) Q :=
      (closedBall_subset_closedBall' (show r + dist x 0 ≤ R by
        have hx' := mem_closedBall.mp hx
        linarith)).trans hRU
    have hEi := X.energy_integrable g he hinj hemb compact
      (closedBall x r) (isCompact_closedBall _ _) hsub
    have hDi : IntegrableOn (fun z => ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2)
        (closedBall x r) := by
      apply integrable_finsetSum
      intro i _
      exact (X.derivative_memLp i _ (isCompact_closedBall _ _) hsub).norm.integrable_sq
    have hlower : (c / 2) *
        (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
          ∫ z in closedBall x r, m65EmbeddedEnergyDensity g e X.value X.derivative z := by
      simpa only [integral_const_mul] using integral_mono_ae (hDi.const_mul (c / 2)) hEi
        (ae_of_all _ fun z => (m65EmbeddedEnergyDensity_bounds g e hb X.value X.derivative z).1)
    have hraw : (∫ z in closedBall x r, ∑ i : Fin 2, ‖X.derivative i z‖ ^ 2) ≤
        (2 / c) * ∫ z in closedBall x r,
          m65EmbeddedEnergyDensity g e X.value X.derivative z := by
      calc
        _ ≤ (∫ z in closedBall x r,
            m65EmbeddedEnergyDensity g e X.value X.derivative z) / (c / 2) := by
          apply (le_div_iff₀ (show 0 < c / 2 by positivity)).mpr
          simpa only [mul_comm] using hlower
        _ = _ := by ring
    calc
      _ ≤ (2 / c) * ∫ z in closedBall x r,
          m65EmbeddedEnergyDensity g e X.value X.derivative z := hraw
      _ ≤ (2 / c) * (B * r ^ α) :=
        mul_le_mul_of_nonneg_left (henergy x hx r hr hrR) (by positivity)
      _ = _ := by rw [show 2 * (α / 2) = α by ring]; ring
  obtain ⟨v, H, hH, hv, hAE, hholder⟩ := X.local_holder_of_energy_decay isOpen_ball 0 hR hRU
    (show 0 < α / 2 by positivity) (show 0 ≤ (2 / c) * B by positivity) hdecay
  refine ⟨R / 8, α / 2, H, v, by positivity, by positivity, by linarith, hH, hv, ?_, hholder⟩
  exact hAE.mono fun z hz => hz.trans (congrArg e (hXv z))






theorem continuous_representative_diameter_trace
    {M : Type*} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (he : Continuous e) (hγ : Continuous γ) (heclosed : IsClosed (range e))
    (F : M65WeakDisk e γ) {p : ℂ} (hp : ‖p‖ = 1)
    {H : ℝ} (hH : 0 < H) (v : LoopPlane → EuclideanSpace ℝ (Fin N))
    (hv : ContinuousOn v (closedBall 0 H))
    (hAE : v =ᵐ[volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1})]
      fun z => e (F.value (diskBoundaryCoordinate p z))) :
    ∃ R : ℝ, 0 < R ∧ R ≤ H ∧ ∀ s ∈ Icc (-R) R,
      v (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        e (γ (F.parameter (boundaryCirclePoint hp s))) := by
  obtain ⟨R0, hR0, hsemi⟩ := weakDisk_boundary_semicircle F he hγ heclosed hp
  let R := min H R0
  have hR : 0 < R := lt_min hH hR0
  have hRH : R ≤ H := min_le_left _ _
  have hRR0 : R ≤ R0 := min_le_right _ _
  let axis := fun s : ℝ => s • EuclideanSpace.basisFun (Fin 2) ℝ 0
  let b := fun s : ℝ => e (γ (F.parameter (boundaryCirclePoint hp s)))
  have haxis : Continuous axis := continuous_id.smul continuous_const
  have hpoint : Continuous (fun s : ℝ => boundaryCirclePoint hp s) := by
    exact ((contDiff_diskBoundaryCoordinate p).continuous.comp haxis).subtype_mk _
  have hb : Continuous b := he.comp (hγ.comp (F.parameter.continuous.comp hpoint))
  have hnorm (s : ℝ) : ‖axis s‖ = |s| := by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one, Real.norm_eq_abs]
  have hvp : ContinuousOn (fun s => v (axis s)) (Icc (0 : ℝ) R) :=
    hv.comp haxis.continuousOn (fun s hs => by
      rw [mem_closedBall_zero_iff, hnorm, abs_of_nonneg hs.1]
      exact hs.2.trans hRH)
  have hvn : ContinuousOn (fun s => v (axis (-s))) (Icc (0 : ℝ) R) :=
    hv.comp (haxis.comp continuous_neg).continuousOn (fun s hs => by
      rw [mem_closedBall_zero_iff, hnorm, abs_neg, abs_of_nonneg hs.1]
      exact hs.2.trans hRH)
  have hpositive (ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
      EqOn (fun s => v (axis s)) b (Icc ε R) ∧
        EqOn (fun s => v (axis (-s))) (fun s => b (-s)) (Icc ε R) := by
    have hgood : ∀ᵐ r ∂volume.restrict (Icc ε R),
        v (axis r) = b r ∧ v (axis (-r)) = b (-r) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Icc_subset_Icc le_rfl hRR0) (hsemi ε hε),
        halfDisk_ae_semicircle hε hRH hAE,
        ae_restrict_mem measurableSet_Icc] with r hrad hpull hr
      obtain ⟨_hD, V, hVAC, hVAE, _hTarget, hV0, hVπ, _hinc, _hgreen⟩ := hrad
      have hrpos : 0 < r := hε.trans_le hr.1
      have hVc : ContinuousOn V (Icc (0 : ℝ) Real.pi) := by
        simpa only [uIcc_of_le Real.pi_pos.le] using hVAC.continuousOn
      have hcircle : Continuous (fun θ : ℝ => r • Proofs.M58.angularPoint θ) :=
        (continuous_const : Continuous (fun _ : ℝ => r)).smul
          Proofs.M58.contDiff_angularPoint.continuous
      have hvcircle : ContinuousOn (fun θ => v (r • Proofs.M58.angularPoint θ))
          (Icc (0 : ℝ) Real.pi) :=
        hv.comp hcircle.continuousOn
          (fun θ _ => by
            rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
              abs_of_pos hrpos, Proofs.M58.norm_angularPoint, mul_one]
            exact hr.2.trans hRH)
      have hboth : V =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
          fun θ => v (r • Proofs.M58.angularPoint θ) := by
        filter_upwards [hVAE, hpull] with θ h1 h2
        exact h1.trans h2.symm
      have hEq := Measure.eqOn_of_ae_eq hboth hVc hvcircle
        (closure_interior_Icc Real.pi_pos.ne).symm.subset
      have hzero : r • Proofs.M58.angularPoint 0 = axis r := by
        ext i
        fin_cases i <;> simp [axis, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
      have hpi : r • Proofs.M58.angularPoint Real.pi = axis (-r) := by
        ext i
        fin_cases i <;> simp [axis, Proofs.M58.angularPoint, EuclideanSpace.basisFun_apply]
      refine ⟨?_, ?_⟩
      · simpa only [hzero] using
          (hEq (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)).symm.trans hV0
      · simpa only [hpi] using
          (hEq (show Real.pi ∈ Icc (0 : ℝ) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩)).symm.trans hVπ
    have hsub : Icc ε R ⊆ Icc (0 : ℝ) R := Icc_subset_Icc hε.le le_rfl
    exact ⟨Measure.eqOn_of_ae_eq (hgood.mono fun _ h => h.1) (hvp.mono hsub) hb.continuousOn
        (closure_interior_Icc hεR.ne).symm.subset,
      Measure.eqOn_of_ae_eq (hgood.mono fun _ h => h.2) (hvn.mono hsub)
        (hb.comp continuous_neg).continuousOn (closure_interior_Icc hεR.ne).symm.subset⟩
  have hpos : EqOn (fun s => v (axis s)) b (Ioc (0 : ℝ) R) := by
    intro s hs
    exact (hpositive (s / 2) (by linarith [hs.1]) (by linarith [hs.1, hs.2])).1
      ⟨by linarith [hs.1], hs.2⟩
  have hneg : EqOn (fun s => v (axis (-s))) (fun s => b (-s)) (Ioc (0 : ℝ) R) := by
    intro s hs
    exact (hpositive (s / 2) (by linarith [hs.1]) (by linarith [hs.1, hs.2])).2
      ⟨by linarith [hs.1], hs.2⟩
  have hclosure : Icc (0 : ℝ) R ⊆ closure (Ioc (0 : ℝ) R) := by
    rw [closure_Ioc hR.ne]
  have hpall := hpos.of_subset_closure hvp hb.continuousOn Ioc_subset_Icc_self hclosure
  have hnall := hneg.of_subset_closure hvn (hb.comp continuous_neg).continuousOn
    Ioc_subset_Icc_self hclosure
  refine ⟨R, hR, hRH, ?_⟩
  intro s hs
  by_cases hspos : 0 ≤ s
  · exact hpall ⟨hspos, hs.2⟩
  · have hn : -s ∈ Icc (0 : ℝ) R := ⟨by linarith, by linarith [hs.1]⟩
    simpa only [neg_neg] using hnall hn






theorem weakDisk_boundary_continuous_representative
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e x))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (γ ∘ m65LoopAngular))
    (hregular : ∀ t, curveVelocity (n := 3) (γ ∘ m65LoopAngular) t ≠ 0)
    (F : M65WeakDisk e γ) (hmin : F.MinimizesEnergy g) {p : ℂ} (hp : ‖p‖ = 1) :
    ∃ (r β H : ℝ) (q : LoopPlane → M),
      0 < r ∧ 0 < β ∧ β < 1 ∧ 0 < H ∧ ContinuousOn q (closedBall 0 r) ∧
      (q =ᵐ[volume.restrict (closedBall 0 r)] fun z =>
        if 0 ≤ z 1 then F.value (diskBoundaryCoordinate p z)
          else F.value (diskBoundaryCoordinate p (boundaryPlaneReflection z))) ∧
      (∀ x ∈ closedBall (0 : LoopPlane) r, ∀ y ∈ closedBall (0 : LoopPlane) r,
        ‖e (q y) - e (q x)‖ ≤ H * dist y x ^ β) ∧
      ∀ s ∈ Icc (-r) r, q (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) =
        γ (F.parameter (boundaryCirclePoint hp s)) := by
  classical
  obtain ⟨R0, β, H, v, hR0, hβ, hβ1, hH, hv, hAE, hholder⟩ :=
    weakDisk_boundary_holder_representative g he hinj hemb compact hγ hsmooth hregular
      F hmin hp
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image he.continuous).isClosed
  have hnonempty : (range e).Nonempty := ⟨e (F.value 0), mem_range_self _⟩
  have hupper : v =ᵐ[volume.restrict (closedBall (0 : LoopPlane) R0 ∩ {z | 0 ≤ z 1})]
      fun z => e (F.value (diskBoundaryCoordinate p z)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hAE,
      ae_restrict_mem (measurableSet_closedBall.inter
        (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet)]
      with z hz hzS
    have hzp : 0 ≤ z 1 := hzS.2
    simpa only [if_pos hzp] using hz
  obtain ⟨R1, hR1, _hR10, htrace⟩ := continuous_representative_diameter_trace
    he.continuous hγ hclosed F hp hR0 v hv hupper
  have hdistAE : (fun z => infDist (v z) (range e)) =ᵐ[volume.restrict (ball 0 R0)]
      fun _ => (0 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hAE] with z hz
    rw [hz]
    exact infDist_zero_of_mem (mem_range_self _)
  have hdist := Measure.eqOn_open_of_ae_eq hdistAE isOpen_ball
    ((continuous_infDist_pt (range e)).comp_continuousOn (hv.mono ball_subset_closedBall))
    continuousOn_const
  have hmem (z : LoopPlane) (hz : z ∈ ball 0 R0) : v z ∈ range e :=
    (hclosed.mem_iff_infDist_zero hnonempty).mpr (hdist hz)
  let : Nonempty M := ⟨F.value 0⟩
  let q : LoopPlane → M := fun z => Function.invFun e (v z)
  have heq : EqOn (e ∘ q) v (ball 0 R0) := by
    intro z hz
    obtain ⟨w, hw⟩ := hmem z hz
    change e (Function.invFun e (v z)) = v z
    rw [← hw]
    exact Function.apply_invFun_apply
  let r := min (R0 / 2) R1
  have hr : 0 < r := lt_min (by positivity) hR1
  have hrr0 : r < R0 := (min_le_left _ _).trans_lt (by linarith)
  have hrr1 : r ≤ R1 := min_le_right _ _
  have hsub : closedBall (0 : LoopPlane) r ⊆ ball 0 R0 := closedBall_subset_ball hrr0
  refine ⟨r, β, H, q, hr, hβ, hβ1, hH, ?_, ?_, ?_, ?_⟩
  · apply hemb.isInducing.continuousOn_iff.mpr
    exact (hv.mono (hsub.trans ball_subset_closedBall)).congr (heq.mono hsub)
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (hsub.trans ball_subset_closedBall) hAE, ae_restrict_mem measurableSet_closedBall]
      with z hz hzr
    exact hemb.injective ((heq (hsub hzr)).trans hz)
  · intro x hx y hy
    change ‖(e ∘ q) y - (e ∘ q) x‖ ≤ _
    rw [heq (hsub hy), heq (hsub hx)]
    exact hholder x (ball_subset_closedBall (hsub hx)) y (ball_subset_closedBall (hsub hy))
  · intro s hs
    apply hemb.injective
    have hnorm : ‖s • EuclideanSpace.basisFun (Fin 2) ℝ 0‖ = |s| := by
      rw [norm_smul, (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one, mul_one, Real.norm_eq_abs]
    have haxis : s • EuclideanSpace.basisFun (Fin 2) ℝ 0 ∈ closedBall (0 : LoopPlane) r := by
      rw [mem_closedBall_zero_iff, hnorm]
      exact abs_le.mpr hs
    exact (heq (hsub haxis)).trans (htrace s (Icc_subset_Icc (neg_le_neg hrr1) hrr1 hs))

end PoincareConjecture.M65Boundary
