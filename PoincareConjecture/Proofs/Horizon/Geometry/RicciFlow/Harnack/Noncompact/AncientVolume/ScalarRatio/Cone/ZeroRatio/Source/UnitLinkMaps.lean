import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceSmooth










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture Manifold
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)


def unitSlicePositiveInclusion (z : AsymptoticConeUnitSlice p hc) :
    AsymptoticConePositive p hc :=
  ⟨z.val, by rw [z.property]; exact zero_lt_one⟩

@[simp] theorem unitSlicePositiveInclusion_val (z : AsymptoticConeUnitSlice p hc) :
    (unitSlicePositiveInclusion hc z).val = z.val := rfl

theorem isometry_unitSlicePositiveInclusion : Isometry (unitSlicePositiveInclusion hc) :=
  fun _ _ => rfl

variable {hc} {n : ℕ}
  (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)



theorem unitSlicePositiveInclusion_smooth_immersion :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (unitSlicePositiveInclusion hc) ∧
      ∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  let D := positiveConePolarDiffeomorph hne hcover
  let j : AsymptoticConeUnitSlice p hc → positiveConeRadii × AsymptoticConeUnitSlice p hc :=
    fun z => (⟨1, by change (0 : ℝ) < 1; norm_num⟩, z)
  have hj : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ j :=
    contMDiff_const.prodMk contMDiff_id
  have heq : D ∘ j = unitSlicePositiveInclusion hc := by
    funext z
    apply Subtype.ext
    change asymptoticConeDilation hc 1 z.val = z.val
    exact asymptoticConeDilation_one hc _
  have hi : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (unitSlicePositiveInclusion hc) := by
    rw [← heq]
    exact D.contMDiff.comp hj
  let N : AsymptoticConePositive p hc → AsymptoticConeUnitSlice p hc :=
    fun a => (D.symm a).2
  have hN : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ N := contMDiff_snd.comp D.symm.contMDiff
  have hleft : N ∘ unitSlicePositiveInclusion hc = id := by
    rw [← heq]
    funext z
    exact congrArg Prod.snd (D.symm_apply_apply (j z))
  refine ⟨hi, fun z => ?_⟩
  have hd := mfderiv_comp z (hN.mdifferentiable (by simp) _) (hi.mdifferentiable (by simp) z)
  rw [hleft, mfderiv_id] at hd
  exact (ContinuousLinearMap.leftInverse_of_comp hd.symm).injective

variable (hc) {Q : Type*} (f : Q → AsymptoticConePositive p hc)
  (hunit : {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆ range f)



def unitSlicePreimage (z : AsymptoticConeUnitSlice p hc) : Q :=
  Classical.choose (hunit (show asymptoticConeRadius hc (unitSlicePositiveInclusion hc z).val = 1
    from z.property))

theorem apply_unitSlicePreimage (z : AsymptoticConeUnitSlice p hc) :
    f (unitSlicePreimage hc f hunit z) = unitSlicePositiveInclusion hc z :=
  Classical.choose_spec (hunit z.property)

theorem unitSlicePreimage_injective :
    Function.Injective (unitSlicePreimage hc f hunit) := by
  intro x y hxy
  apply (isometry_unitSlicePositiveInclusion hc).injective
  rw [← apply_unitSlicePreimage hc f hunit, ← apply_unitSlicePreimage hc f hunit, hxy]

theorem range_unitSlicePreimage (hf : Function.Injective f) :
    range (unitSlicePreimage hc f hunit) =
      f ⁻¹' {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    change asymptoticConeRadius hc (f (unitSlicePreimage hc f hunit z)).val = 1
    rw [apply_unitSlicePreimage hc f hunit z]
    exact z.property
  · intro hq
    refine ⟨⟨(f q).val, hq⟩, hf ?_⟩
    rw [apply_unitSlicePreimage hc f hunit]
    rfl



def sourceUnitSliceMap {M : Type*} (A : Q → M) : AsymptoticConeUnitSlice p hc → M :=
  A ∘ unitSlicePreimage hc f hunit

theorem range_sourceUnitSliceMap {M : Type*} (A : Q → M) (hf : Function.Injective f) :
    range (sourceUnitSliceMap hc f hunit A) =
      A '' (f ⁻¹' {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1}) := by
  rw [sourceUnitSliceMap, range_comp, range_unitSlicePreimage hc f hunit hf]




theorem unitSlicePreimage_smooth_immersion
    [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Q]
    [IsManifold (𝓡 (n + 1)) ∞ Q] (hf : Topology.IsOpenEmbedding f) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ f →
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (unitSlicePreimage hc f hunit) ∧
      ∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePreimage hc f hunit) z) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro hfsmooth
  obtain ⟨hi, hdi⟩ := unitSlicePositiveInclusion_smooth_immersion hne hcover
  have hb : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (unitSlicePreimage hc f hunit) := by
    intro z
    let : Nonempty Q := ⟨unitSlicePreimage hc f hunit z⟩
    have heq : unitSlicePreimage hc f hunit = Function.invFun f ∘ unitSlicePositiveInclusion hc := by
      funext w
      apply hf.injective
      rw [apply_unitSlicePreimage hc f hunit w, Function.comp_apply,
        Function.invFun_eq (hunit w.property)]
    rw [heq]
    exact ((ChartDistance.contMDiffOn_invFun_of_localDiffeomorph hfsmooth hf.injective).contMDiffAt
      (hf.isOpen_range.mem_nhds (hunit z.property))).comp z (hi z)
  refine ⟨hb, fun z => ?_⟩
  have heq : f ∘ unitSlicePreimage hc f hunit = unitSlicePositiveInclusion hc :=
    funext (apply_unitSlicePreimage hc f hunit)
  have hd := mfderiv_comp z (hfsmooth.mdifferentiable (by simp) _) (hb.mdifferentiable (by simp) z)
  rw [heq] at hd
  have hinj : Function.Injective ((mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f
      (unitSlicePreimage hc f hunit z)).comp
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePreimage hc f hunit) z)) := by
    rw [← hd]
    exact hdi z
  intro u v huv
  apply hinj
  exact congrArg (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f
    (unitSlicePreimage hc f hunit z)) huv




theorem eventually_sourceUnitSliceMap_smooth_embedding
    [ProperSpace X] [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Q]
    [IsManifold (𝓡 (n + 1)) ∞ Q]
    (hf : Topology.IsOpenEmbedding f)
    {V : Set Q} (_hV : IsOpen V)
    (hunitV : f ⁻¹' {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆ V)
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, T2Space (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (M k)]
    [∀ k, IsManifold (𝓡 (n + 1)) ∞ (M k)]
    (A : ∀ k, Q → M k)
    (hA : ∀ᶠ k in atTop, Topology.IsOpenEmbedding (fun q : V => A k q) ∧
      IsLocalDiffeomorphOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (A k) V) :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ f →
      ∀ᶠ k in atTop,
        ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (sourceUnitSliceMap hc f hunit (A k)) ∧
        Topology.IsClosedEmbedding (sourceUnitSliceMap hc f hunit (A k)) ∧
        (∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1))
          (sourceUnitSliceMap hc f hunit (A k)) z)) ∧
        IsCompact (range (sourceUnitSliceMap hc f hunit (A k))) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro hfsmooth
  obtain ⟨hb, hdb⟩ := unitSlicePreimage_smooth_immersion
    (hc := hc) (hne := hne) (hcover := hcover) f hunit hf hfsmooth
  have hbV (z : AsymptoticConeUnitSlice p hc) : unitSlicePreimage hc f hunit z ∈ V := by
    apply hunitV
    change asymptoticConeRadius hc (f (unitSlicePreimage hc f hunit z)).val = 1
    rw [apply_unitSlicePreimage hc f hunit z]
    exact z.property
  filter_upwards [hA] with k hk
  have hlocal (z : AsymptoticConeUnitSlice p hc) := hk.2 ⟨unitSlicePreimage hc f hunit z, hbV z⟩
  have hs : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (sourceUnitSliceMap hc f hunit (A k)) :=
    fun z => (hlocal z).contMDiffAt.comp z (hb z)
  have hinj : Function.Injective (sourceUnitSliceMap hc f hunit (A k)) := by
    intro z w hzw
    apply unitSlicePreimage_injective hc f hunit
    exact congrArg Subtype.val (hk.1.injective
      (a₁ := ⟨unitSlicePreimage hc f hunit z, hbV z⟩)
      (a₂ := ⟨unitSlicePreimage hc f hunit w, hbV w⟩) hzw)
  refine ⟨hs, hs.continuous.isClosedEmbedding hinj, ?_, isCompact_range hs.continuous⟩
  intro z
  change Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (A k ∘ unitSlicePreimage hc f hunit) z)
  rw [mfderiv_comp z ((hlocal z).mdifferentiableAt (by simp)) (hb.mdifferentiable (by simp) z)]
  exact ((hlocal z).mfderivToContinuousLinearEquiv (by simp)).injective.comp (hdb z)

end Poincare.AncientVolume.ScalarRatio
