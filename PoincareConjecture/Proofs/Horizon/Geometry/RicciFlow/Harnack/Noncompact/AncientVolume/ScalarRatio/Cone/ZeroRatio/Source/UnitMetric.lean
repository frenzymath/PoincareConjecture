import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.UnitPotential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture Manifold
open scoped Manifold ContDiff Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} {hc : RayComparison p} {n : ℕ}
  (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)

theorem unitSlicePositiveInclusion_inner :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ z (v w : TangentSpace (𝓡 n) z),
      (unitSliceMetric hcover).inner z v w =
        (positiveConeMetric hne hcover).inner (unitSlicePositiveInclusion hc z)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z w) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  let r : positiveConeRadii := ⟨1, by change (0 : ℝ) < 1; norm_num⟩
  let j : AsymptoticConeUnitSlice p hc → positiveConeRadii × AsymptoticConeUnitSlice p hc :=
    fun z => (r, z)
  have hj : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ j :=
    contMDiff_const.prodMk contMDiff_id
  have hpolar := isLocalDiffeomorph_positiveConePolarMap hne hcover
  have heq : positiveConePolarMap hc ∘ j = unitSlicePositiveInclusion hc := by
    funext z
    apply Subtype.ext
    exact asymptoticConeDilation_one hc z.val
  intro z v w
  have hdj (a : TangentSpace (𝓡 n) z) :
      mfderiv (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) j z a = (0, a) := by
    change mfderiv (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) (fun y => (r, y)) z a = _
    have hd := mfderiv_prodMk (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n)
      (f := fun _ : AsymptoticConeUnitSlice p hc => r) (g := id) (x := z)
      mdifferentiableAt_const mdifferentiableAt_id
    have hh := congrArg (fun L => L a) hd
    simp only [mfderiv_const, mfderiv_id] at hh
    convert! hh using 1
  have hd := mfderiv_comp z (hpolar.mdifferentiable (by simp) (j z))
    (hj.mdifferentiable (by simp) z)
  rw [heq] at hd
  have hv := congrArg (fun L => L v) hd
  have hw := congrArg (fun L => L w) hd
  change mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z v =
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) (j z)
      (mfderiv (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) j z v) at hv
  change mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z w =
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) (j z)
      (mfderiv (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) j z w) at hw
  rw [hdj] at hv hw
  have hm := positiveConePolarMap_inner hne hcover (j z) 0 0 v w
  have hbase : positiveConePolarMap hc (j z) = unitSlicePositiveInclusion hc z :=
    congrFun heq z
  calc
    (unitSliceMetric hcover).inner z v w =
        (positiveConeMetric hne hcover).inner (positiveConePolarMap hc (j z))
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) (j z) (0, v))
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (positiveConePolarMap hc) (j z) (0, w)) := by
      simpa [j, r] using hm.symm
    _ = (positiveConeMetric hne hcover).inner (positiveConePolarMap hc (j z))
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z w) :=
      congrArg₂ (fun a b : EuclideanSpace ℝ (Fin (n + 1)) =>
        (positiveConeMetric hne hcover).inner (positiveConePolarMap hc (j z)) a b) hv.symm hw.symm
    _ = _ := congrArg (fun q : AsymptoticConePositive p hc =>
      (positiveConeMetric hne hcover).inner q
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z v)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z w)) hbase

variable (hc) [ProperSpace X]
    {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Q] [IsManifold (𝓡 (n + 1)) ∞ Q]
    (f : Q → AsymptoticConePositive p hc) (hf : Topology.IsOpenEmbedding f)
    (hunit : {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆ range f)
    (V : TopologicalSpace.Opens Q)
    (hKV : f ⁻¹' {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆ V)

include hf in

theorem unitSlicePreimageInOpen_inner :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ hlocal : IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ f,
    let gQ := (positiveConeMetric hne hcover).pullbackOfLocalDiffeomorph f hlocal
    let gV := gQ.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) V)
    ∀ z (v w : TangentSpace (𝓡 n) z),
      (unitSliceMetric hcover).inner z v w =
        gV.inner (unitSlicePreimageInOpen hc f hunit V hKV z)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePreimageInOpen hc f hunit V hKV) z v)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePreimageInOpen hc f hunit V hKV) z w) := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro hlocal
  dsimp only
  let gQ := (positiveConeMetric hne hcover).pullbackOfLocalDiffeomorph f hlocal
  let he := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) V
  let gV := gQ.pullbackOfLocalDiffeomorph Subtype.val he
  let b := unitSlicePreimageInOpen hc f hunit V hKV
  let A : V → AsymptoticConePositive p hc := f ∘ Subtype.val
  have hA : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ A := hlocal.contMDiff.comp he.contMDiff
  have hb := (unitSlicePreimageInOpen_geometry hc hne hcover f hf hunit V hKV hlocal).1
  have hm (x : V) (a d : TangentSpace (𝓡 (n + 1)) x) :
      gV.inner x a d = (positiveConeMetric hne hcover).inner (A x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) A x a)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) A x d) := by
    rw [show A = f ∘ Subtype.val from rfl,
      mfderiv_comp x (hlocal.mdifferentiable (by simp) x.val) (he.mdifferentiable (by simp) x)]
    rfl
  have hAb : A ∘ b = unitSlicePositiveInclusion hc := funext (apply_unitSlicePreimage hc f hunit)
  intro z v w
  change (unitSliceMetric hcover).inner z v w = gV.inner (b z)
    (mfderiv (𝓡 n) (𝓡 (n + 1)) b z v) (mfderiv (𝓡 n) (𝓡 (n + 1)) b z w)
  rw [hm]
  have hd := mfderiv_comp z (hA.mdifferentiable (by simp) (b z)) (hb.mdifferentiable (by simp) z)
  rw [hAb] at hd
  have hdv (a : TangentSpace (𝓡 n) z) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) A (b z) (mfderiv (𝓡 n) (𝓡 (n + 1)) b z a) =
        mfderiv (𝓡 n) (𝓡 (n + 1)) (unitSlicePositiveInclusion hc) z a :=
    (congrArg (fun L => L a) hd).symm
  rw [hdv, hdv]
  rw [show A (b z) = unitSlicePositiveInclusion hc z from congrFun hAb z]
  exact unitSlicePositiveInclusion_inner hne hcover z v w

end Poincare.AncientVolume.ScalarRatio
