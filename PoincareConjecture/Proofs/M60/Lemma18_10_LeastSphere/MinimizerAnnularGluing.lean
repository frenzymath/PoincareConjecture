import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularCap
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaCoordinateCompactness
import PoincareConjecture.Proofs.M58.Mathlib.LocalContraction
import PoincareConjecture.Proofs.M58.Mathlib.CompactRiemannianBallBundle
import PoincareConjecture.Proofs.M58.Cor18_28_DiskExtension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Real
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

private def annularTime (R d r : ℝ) : ℝ :=
  smoothTransition ((r - (R - d)) / (2 * d))

private theorem annularTime_smooth (R d : ℝ) : ContDiff ℝ ∞ (annularTime R d) :=
  smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

private theorem annularTime_mem (R d r : ℝ) : annularTime R d r ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

private theorem annularTime_zero {R d r : ℝ} (hd : 0 < d) (hr : r ≤ R - d) :
    annularTime R d r = 0 :=
  smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hr) (by positivity))

private theorem annularTime_one {R d r : ℝ} (hd : 0 < d) (hr : R + d ≤ r) :
    annularTime R d r = 1 := by
  apply smoothTransition.one_of_one_le
  exact (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr (by linarith only [hr])

variable {M : Type*}



def suAnnularBlend (C : ℝ × (M × M) → M) (f a : LoopPlane → M)
    (R d : ℝ) (z : LoopPlane) : M :=
  if R + d ≤ ‖z‖ then f z else if ‖z‖ ≤ R - d then a z
    else C (annularTime R d ‖z‖, f z, a z)


theorem suAnnularBlend_outer (C : ℝ × (M × M) → M) (f a : LoopPlane → M)
    {R d : ℝ} {z : LoopPlane} (hz : R + d ≤ ‖z‖) :
    suAnnularBlend C f a R d z = f z := by simp only [suAnnularBlend, if_pos hz]


theorem suAnnularBlend_inner (C : ℝ × (M × M) → M) (f a : LoopPlane → M)
    {R d : ℝ} (hd : 0 < d) {z : LoopPlane} (hz : ‖z‖ ≤ R - d) :
    suAnnularBlend C f a R d z = a z := by
  rw [suAnnularBlend, if_neg (by linarith only [hz, hd]), if_pos hz]

private theorem annularBlend_eq_contraction
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h0 : ∀ p q, C (0, p, q) = q) (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (f a : LoopPlane → M) {R d : ℝ} (hd : 0 < d) {z : LoopPlane}
    (hz : (f z, a z) ∈ U) :
    suAnnularBlend C f a R d z = C (annularTime R d ‖z‖, f z, a z) := by
  dsimp only [suAnnularBlend]
  split_ifs with hout hin
  · rw [annularTime_one hd hout, h1 _ hz]
  · rw [annularTime_zero hd hin, h0]
  · rfl

variable {n : ℕ} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in



theorem suAnnularBlend_contMDiff
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h0 : ∀ p q, C (0, p, q) = q) (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ U,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 C (t, v))
    {f a : LoopPlane → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (ha : ContMDiff (𝓡 2) (𝓡 n) 1 a) {R d : ℝ} (hd : 0 < d) (hRd : 2 * d < R)
    (hpairs : ∀ z : LoopPlane, R - 2 * d < ‖z‖ → ‖z‖ < R + 2 * d → (f z, a z) ∈ U) :
    ContMDiff (𝓡 2) (𝓡 n) 1 (suAnnularBlend C f a R d) := by
  intro z
  by_cases hout : R + d < ‖z‖
  · apply (hf z).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hout] with w hw
    exact suAnnularBlend_outer C f a hw.le
  by_cases hin : ‖z‖ < R - d
  · apply (ha z).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hin] with w hw
    exact suAnnularBlend_inner C f a hd hw.le
  have hlo : R - d ≤ ‖z‖ := le_of_not_gt hin
  have hhi : ‖z‖ ≤ R + d := le_of_not_gt hout
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith only [hlo, hRd, hd])
  have htime : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1 (fun w : LoopPlane => annularTime R d ‖w‖) z :=
    (((annularTime_smooth R d).contDiffAt.comp z (contDiffAt_norm ℝ hz0)).of_le
      (by simp)).contMDiffAt
  have hpair := hpairs z (by linarith only [hlo, hd]) (by linarith only [hhi, hd])
  apply ((hC _ (annularTime_mem R d ‖z‖) _ hpair).comp z
    (htime.prodMk ((hf z).prodMk (ha z)))).congr_of_eventuallyEq
  have hlo' : R - 2 * d < ‖z‖ := by linarith only [hlo, hd]
  have hhi' : ‖z‖ < R + 2 * d := by linarith only [hhi, hd]
  have hnear : ∀ᶠ w in 𝓝 z, R - 2 * d < ‖w‖ ∧ ‖w‖ < R + 2 * d :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hlo', hhi'⟩
  filter_upwards [hnear] with w hw
  exact annularBlend_eq_contraction C h0 h1 f a hd (hpairs w hw.1 hw.2)




def suSpherePlanePatch (f : UnitTwoSphere → M) (c : UnitTwoSphere)
    (F : LoopPlane → M) (p : UnitTwoSphere) : M := by
  classical
  exact if p ∈ (chartAt LoopPlane c).source then F (chartAt LoopPlane c p) else f p

omit [TopologicalSpace M] in


theorem suSpherePlanePatch_parameter (f : UnitTwoSphere → M) (c : UnitTwoSphere)
    (F : LoopPlane → M) (z : LoopPlane) :
    suSpherePlanePatch f c F ((chartAt LoopPlane c).symm z) = F z := by
  classical
  have ht : z ∈ (chartAt LoopPlane c).target := by rw [suSphereChart_target]; trivial
  rw [suSpherePlanePatch, if_pos ((chartAt LoopPlane c).map_target ht),
    (chartAt LoopPlane c).right_inv ht]

omit [TopologicalSpace M] in


theorem suSpherePlanePatch_outside (f : UnitTwoSphere → M) (c : UnitTwoSphere)
    {F : LoopPlane → M} {R : ℝ}
    (hF : ∀ z : LoopPlane, R < ‖z‖ → F z = f ((chartAt LoopPlane c).symm z))
    {p : UnitTwoSphere} (hp : p ∉ (chartAt LoopPlane c).symm '' closedBall (0 : LoopPlane) R) :
    suSpherePlanePatch f c F p = f p := by
  classical
  dsimp only [suSpherePlanePatch]
  split_ifs with hx
  · have hz : R < ‖chartAt LoopPlane c p‖ := by
      by_contra h
      exact hp ⟨chartAt LoopPlane c p, mem_closedBall_zero_iff.mpr (le_of_not_gt h),
        (chartAt LoopPlane c).left_inv hx⟩
    rw [hF _ hz, (chartAt LoopPlane c).left_inv hx]
  · rfl

omit [IsManifold (𝓡 n) ∞ M] in



theorem suSpherePlanePatch_contMDiff
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (c : UnitTwoSphere)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 n) 1 F) {R : ℝ}
    (hout : ∀ z : LoopPlane, R < ‖z‖ → F z = f ((chartAt LoopPlane c).symm z)) :
    ContMDiff (𝓡 2) (𝓡 n) 1 (suSpherePlanePatch f c F) := by
  classical
  let e := chartAt LoopPlane c
  let K := e.symm '' closedBall (0 : LoopPlane) R
  have hK : IsCompact K := (isCompact_closedBall (0 : LoopPlane) R).image
    (suSphereChart_smooth c).continuous
  have hKsource : K ⊆ e.source := by
    rintro _ ⟨z, _, rfl⟩
    apply e.map_target
    rw [suSphereChart_target]
    trivial
  intro p
  by_cases hp : p ∈ e.source
  · have hech : ContMDiffOn (𝓡 2) (𝓡 2) 1 e e.source := contMDiffOn_chart
    have he : ContMDiffAt (𝓡 2) (𝓡 2) 1 e p :=
      hech.contMDiffAt (e.open_source.mem_nhds hp)
    apply ((hF (e p)).comp p he).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact if_pos hq
  · have hpK : p ∉ K := fun h => hp (hKsource h)
    apply (hf p).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hpK] with q hq
    exact suSpherePlanePatch_outside f c hout hq

omit [IsManifold (𝓡 n) ∞ M] in



theorem suSphere_annular_candidate
    (C : ℝ × (M × M) → M) {U : Set (M × M)}
    (h0 : ∀ p q, C (0, p, q) = q) (h1 : ∀ v ∈ U, C (1, v) = v.1)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ U,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 C (t, v))
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (c : UnitTwoSphere) {s : ℝ} (hs : 0 < s)
    {a : LoopPlane → M} (ha : ContMDiff (𝓡 2) (𝓡 n) 1 a)
    {R d : ℝ} (hd : 0 < d) (hRd : 2 * d < R)
    (hpairs : ∀ z : LoopPlane, R - 2 * d < ‖z‖ → ‖z‖ < R + 2 * d →
      (f ((chartAt LoopPlane c).symm (s • z)), a z) ∈ U) :
    ∃ h : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 h ∧
      (∀ z : LoopPlane, h ((chartAt LoopPlane c).symm (s • z)) =
        suAnnularBlend C (fun y => f ((chartAt LoopPlane c).symm (s • y))) a R d z) ∧
      ∀ p ∉ (chartAt LoopPlane c).symm '' closedBall (0 : LoopPlane) (s * (R + d)),
        h p = f p := by
  let F := fun z : LoopPlane => f ((chartAt LoopPlane c).symm (s • z))
  let B := suAnnularBlend C F a R d
  have hF : ContMDiff (𝓡 2) (𝓡 n) 1 F :=
    hf.comp (((suSphereChart_smooth c).of_le (by simp)).comp
      ((s • ContinuousLinearMap.id ℝ LoopPlane).contDiff.contMDiff))
  have hB : ContMDiff (𝓡 2) (𝓡 n) 1 B :=
    suAnnularBlend_contMDiff C h0 h1 hC hF ha hd hRd hpairs
  let P := fun z : LoopPlane => B (s⁻¹ • z)
  have hP : ContMDiff (𝓡 2) (𝓡 n) 1 P :=
    hB.comp ((s⁻¹ • ContinuousLinearMap.id ℝ LoopPlane).contDiff.contMDiff)
  have hout (z : LoopPlane) (hz : s * (R + d) < ‖z‖) :
      P z = f ((chartAt LoopPlane c).symm z) := by
    have hr : R + d ≤ ‖s⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), ← div_eq_inv_mul]
      exact ((lt_div_iff₀ hs).mpr (by nlinarith only [hz])).le
    change suAnnularBlend C F a R d (s⁻¹ • z) = _
    rw [suAnnularBlend_outer C F a hr]
    change f ((chartAt LoopPlane c).symm (s • (s⁻¹ • z))) = _
    rw [smul_inv_smul₀ hs.ne']
  refine ⟨suSpherePlanePatch f c P, suSpherePlanePatch_contMDiff hf c hP hout, ?_,
    fun p hp => suSpherePlanePatch_outside f c hout hp⟩
  intro z
  rw [suSpherePlanePatch_parameter]
  change B (s⁻¹ • (s • z)) = B z
  rw [inv_smul_smul₀ hs.ne']

section Contraction

open Bundle

private theorem annular_time_input :
    Continuous (fun v : ℝ × (M × M) =>
      (⟨v, (1, 0, 0)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (ℝ × (M × M)))) := by
  have ht : Continuous (fun v : ℝ × (M × M) =>
      (⟨v.1, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_fst.prodMk continuous_const)
  have hp : Continuous (fun v : ℝ × (M × M) =>
      (⟨v.2, 0⟩ : TangentBundle ((𝓡 n).prod (𝓡 n)) (M × M))) :=
    (Bundle.Trivialization.continuous_zeroSection ℝ).comp continuous_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
    (I' := (𝓡 n).prod (𝓡 n)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
      (ht.prodMk hp)

private theorem annular_endpoint_input :
    Continuous (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
      (⟨(v.1, v.2.1.proj, v.2.2.proj), (0, v.2.1.2, v.2.2.2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (ℝ × (M × M)))) := by
  have ht : Continuous
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        (⟨v.1, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_fst.prodMk continuous_const)
  have hp : Continuous
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        (⟨(v.2.1.proj, v.2.2.proj), (v.2.1.2, v.2.2.2)⟩ :
          TangentBundle ((𝓡 n).prod (𝓡 n)) (M × M))) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓡 n) (I' := 𝓡 n)
      (M := M) (M' := M) (n := 0)).continuous.comp continuous_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
    (I' := (𝓡 n).prod (𝓡 n)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
      (ht.prodMk hp)

private theorem annular_endpoint_bound [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) (C : ℝ × (M × M) → M)
    {L : Set (M × M)} (hL : IsCompact L)
    (hC : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 C x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ∀ v : TangentSpace (𝓡 n) x.2.1, ∀ w : TangentSpace (𝓡 n) x.2.2,
        g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x (0, v, w)) ≤
            B * (g.tangentNorm x.2.1 v + g.tangentNorm x.2.2 w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C
  let Q : Set (TangentBundle (𝓡 n) M) := {v | v.proj ∈ (univ : Set M) ∧ ‖v.2‖ ≤ 1}
  have hQ : IsCompact Q := Proofs.M58.isCompact_bundle_norm_le isCompact_univ 1
  let S : Set (ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M)) :=
    (Icc (0 : ℝ) 1 ×ˢ (Q ×ˢ Q)) ∩ {v | (v.2.1.proj, v.2.2.proj) ∈ L}
  have hproj : Continuous
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        (v.2.1.proj, v.2.2.proj)) :=
    ((FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))).comp
      continuous_snd.fst).prodMk
        ((FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))).comp
          continuous_snd.snd)
  have hS : IsCompact S := (isCompact_Icc.prod (hQ.prod hQ)).inter_right
    (hL.isClosed.preimage hproj)
  have hc : ContinuousOn
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        ‖D (v.1, v.2.1.proj, v.2.2.proj) (0, v.2.1.2, v.2.2.2)‖) S := by
    intro v hv
    have hbase : (v.1, v.2.1.proj, v.2.2.proj) ∈ Icc (0 : ℝ) 1 ×ˢ L :=
      ⟨hv.1.1, hv.2⟩
    exact (Proofs.M58.continuous_bundle_norm.continuousAt.comp
      ((Proofs.M58.continuousAt_tangentMap_of_contMDiffAt
        (hC _ hbase)).comp annular_endpoint_input.continuousAt)).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx v w
  change ‖D x (0, v, w)‖ ≤ max B 0 * (‖v‖ + ‖w‖)
  let N := ‖v‖ + ‖w‖
  by_cases hN : N = 0
  · have hv : v = 0 := norm_eq_zero.mp (by
      dsimp only [N] at hN
      linarith [norm_nonneg v, norm_nonneg w])
    have hw : w = 0 := norm_eq_zero.mp (by
      dsimp only [N] at hN
      linarith [norm_nonneg v, norm_nonneg w])
    subst v
    subst w
    change ‖D x 0‖ ≤ _
    rw [map_zero, norm_zero]
    positivity
  have hNpos : 0 < N := lt_of_le_of_ne (add_nonneg (norm_nonneg v) (norm_nonneg w))
    (Ne.symm hN)
  let v' := N⁻¹ • v
  let w' := N⁻¹ • w
  have hv' : ‖v'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hNpos.le), ← div_eq_inv_mul]
    exact (div_le_one hNpos).mpr (le_add_of_nonneg_right (norm_nonneg w))
  have hw' : ‖w'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hNpos.le), ← div_eq_inv_mul]
    exact (div_le_one hNpos).mpr (le_add_of_nonneg_left (norm_nonneg v))
  have hmem : (x.1, (⟨x.2.1, v'⟩ : TangentBundle (𝓡 n) M),
      (⟨x.2.2, w'⟩ : TangentBundle (𝓡 n) M)) ∈ S :=
    ⟨⟨hx.1, ⟨mem_univ _, hv'⟩, ⟨mem_univ _, hw'⟩⟩, hx.2⟩
  have hb : ‖D x (0, v', w')‖ ≤ max B 0 :=
    (le_abs_self _).trans ((hB _ hmem).trans (le_max_left _ _))
  have heq : (0, v', w') = N⁻¹ •
      ((0, v, w) : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) x) := by
    simp only [Prod.smul_mk, smul_zero, v', w']
  erw [heq, map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hNpos.le)] at hb
  exact (div_le_iff₀ hNpos).mp (by simpa only [div_eq_mul_inv, mul_comm] using hb)

set_option maxHeartbeats 400000 in





theorem suAnnular_contraction [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) :
    ∃ (C : ℝ × (M × M) → M) (U : Set (M × M)) (B : ℝ),
      IsOpen U ∧ diagonal M ⊆ U ∧ 0 ≤ B ∧
      (∀ p q, C (0, p, q) = q) ∧ (∀ v ∈ U, C (1, v) = v.1) ∧
      (∀ t p, C (t, p, p) = p) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
        ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 C x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
        ∀ v : TangentSpace (𝓡 n) x.2.1, ∀ w : TangentSpace (𝓡 n) x.2.2,
          g.tangentNorm (C x)
            (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x (0, v, w)) ≤
              B * (g.tangentNorm x.2.1 v + g.tangentNorm x.2.2 w)) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ V : Set (M × M),
        IsOpen V ∧ diagonal M ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ V, g.tangentNorm (C x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x (1, 0, 0)) < epsilon := by
  obtain ⟨C, U, hU, hdiag, h0, h1, hfix, hC⟩ :=
    Proofs.M58.exists_local_contraction (𝓡 n) (isCompact_univ : IsCompact (univ : Set M)) 1
  obtain ⟨L, hL, hdiagL, hLU⟩ :=
    exists_compact_between (isCompact_diagonal (X := M)) hU hdiag
  have hCL : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 C x :=
    fun x hx => hC x ⟨hx.1, hLU hx.2⟩
  obtain ⟨B, hB, hb⟩ := annular_endpoint_bound g C hL hCL
  refine ⟨C, interior L, B, isOpen_interior, hdiagL, hB, h0,
    (fun v hv => h1 v (hLU (interior_subset hv))), hfix,
    (fun x hx => hCL x ⟨hx.1, interior_subset hx.2⟩),
    (fun x hx => hb x ⟨hx.1, interior_subset hx.2⟩), ?_⟩
  intro epsilon hepsilon
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let A := fun x => g.tangentNorm (C x)
    (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x (1, 0, 0))
  let W := interior {x | A x < epsilon}
  have hW : Icc (0 : ℝ) 1 ×ˢ diagonal M ⊆ W := by
    rintro ⟨t, p, q⟩ ⟨ht, hpq⟩
    have hpq' : p = q := hpq
    subst q
    have hc := hC (t, p, p) ⟨ht, hdiag rfl⟩
    have hi : MDifferentiableAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (fun s : ℝ => (s, p, p)) t :=
      mdifferentiableAt_id.prodMk (mdifferentiableAt_const.prodMk mdifferentiableAt_const)
    have hd := mfderiv_comp_apply t (hc.mdifferentiableAt one_ne_zero) hi (1 : ℝ)
    have heq : C ∘ (fun s : ℝ => (s, p, p)) = fun _ : ℝ => p := funext (fun s => hfix s p)
    rw [heq, mfderiv_const] at hd
    erw [mfderiv_prodMk mdifferentiableAt_id
      (mdifferentiableAt_const.prodMk mdifferentiableAt_const),
      mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_const] at hd
    simp only [mfderiv_id, mfderiv_const] at hd
    have hdz : mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C
        (t, p, p) (1, 0, 0) = 0 := by
      change (0 : EuclideanSpace ℝ (Fin n)) =
        mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C
          (t, p, p) (1, 0, 0) at hd
      exact hd.symm
    have hzero : A (t, p, p) = 0 := by
      dsimp only [A]
      rw [hdz]
      change ‖(0 : TangentSpace (𝓡 n) (C (t, p, p)))‖ = 0
      exact norm_zero
    have hcont : ContinuousAt A (t, p, p) :=
      Proofs.M58.continuous_bundle_norm.continuousAt.comp
        ((Proofs.M58.continuousAt_tangentMap_of_contMDiffAt hc).comp
          annular_time_input.continuousAt)
    apply mem_interior_iff_mem_nhds.mpr
    exact hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds
      (by change A (t, p, p) < epsilon; rwa [hzero]))
  obtain ⟨T, V, _, hV, hT, hVdiag, hTV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_diagonal isOpen_interior hW
  refine ⟨V ∩ interior L, hV.inter isOpen_interior, subset_inter hVdiag hdiagL,
    inter_subset_right, ?_⟩
  intro x hx
  have hh : x ∈ {x | A x < epsilon} := interior_subset (hTV ⟨hT hx.1, hx.2.1⟩)
  exact hh

end Contraction

end PoincareConjecture.M60
