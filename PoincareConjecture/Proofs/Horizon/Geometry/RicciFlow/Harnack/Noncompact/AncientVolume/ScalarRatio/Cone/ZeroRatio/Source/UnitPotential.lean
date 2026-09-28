import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.UnitLinkMaps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Shape.Transport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture Manifold
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

theorem radialPotential_on_open
    {n : ℕ} {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]
    (g : RiemannianMetric n Q) (u : Q → ℝ)
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hH : ∀ x v w, g.leviCivitaData.hessian u x v w = g.inner x v w)
    (hQ : ∀ x, g.leviCivitaData.levelQ u x = 2 * u x)
    (V : TopologicalSpace.Opens Q) :
    let gV := g.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V)
    let uV := fun x : V => u x
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ uV ∧
      (∀ x v w, gV.leviCivitaData.hessian uV x v w = gV.inner x v w) ∧
      ∀ x, gV.leviCivitaData.levelQ uV x = 2 * uV x := by
  let e : V → Q := Subtype.val
  let he := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V
  let gV := g.pullbackOfLocalDiffeomorph e he
  have hinv (x : V) : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible :=
    ⟨(he x).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hmetric (x : V) (v w : TangentSpace (𝓡 n) x) :
      gV.inner x v w = g.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) := rfl
  refine ⟨hu.comp he.contMDiff, ?_, ?_⟩
  · intro x v w
    have hh := gV.leviCivitaData.hessian_comp_of_metric_pullback g.leviCivitaData
      (he.contMDiff x) (.of_forall hinv) (.of_forall hmetric) (hu (e x)) v w
    rw [hH] at hh
    exact hh.trans (hmetric x v w).symm
  · intro x
    exact (gV.leviCivitaData.levelQ_comp_of_metric_pullback g.leviCivitaData
      (he.mdifferentiable (by simp) x) (hinv x) (hmetric x)
      (hu.mdifferentiable (by simp) (e x))).trans (hQ (e x))

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] [ProperSpace X] {p : X}
    (hc : RayComparison p) {n : ℕ}
    (hne : Nonempty (AsymptoticConePositive p hc))
    (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
      ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)
    {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Q] [IsManifold (𝓡 (n + 1)) ∞ Q]
    (f : Q → AsymptoticConePositive p hc) (hf : Topology.IsOpenEmbedding f)
    (hunit : {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆ range f)
    (V : TopologicalSpace.Opens Q)
    (hKV : f ⁻¹' {a : AsymptoticConePositive p hc | asymptoticConeRadius hc a.val = 1} ⊆ V)

def unitSlicePreimageInOpen (z : AsymptoticConeUnitSlice p hc) : V :=
  ⟨unitSlicePreimage hc f hunit z, hKV (by
    change asymptoticConeRadius hc (f (unitSlicePreimage hc f hunit z)).val = 1
    rw [apply_unitSlicePreimage hc f hunit]
    exact z.property)⟩

omit [ProperSpace X] in
@[simp] theorem unitSlicePreimageInOpen_val (z : AsymptoticConeUnitSlice p hc) :
    (unitSlicePreimageInOpen hc f hunit V hKV z).val = unitSlicePreimage hc f hunit z := rfl

include hf in
theorem unitSlicePreimageInOpen_geometry :
    letI := unitSliceChartedSpace hc n hcover
    letI := unitSlice_isManifold hc n hcover
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ f →
      ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (unitSlicePreimageInOpen hc f hunit V hKV) ∧
      (∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1))
        (unitSlicePreimageInOpen hc f hunit V hKV) z)) ∧
      IsCompact (range (unitSlicePreimageInOpen hc f hunit V hKV)) ∧
      ∀ z, positiveConeRadialPotential hc
        (f (unitSlicePreimageInOpen hc f hunit V hKV z)) = 1 / 2 := by
  let := unitSliceChartedSpace hc n hcover
  let := unitSlice_isManifold hc n hcover
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro hlocal
  obtain ⟨hb, hdb⟩ := unitSlicePreimage_smooth_immersion
    (hne := hne) (hcover := hcover) hc f hunit hf hlocal
  let b := unitSlicePreimageInOpen hc f hunit V hKV
  have hs : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ b := by
    intro z
    exact (ContMDiffAt.subtypeVal_comp_iff V b z).mp (hb z)
  refine ⟨hs, ?_, isCompact_range hs.continuous, ?_⟩
  · intro z v w hvw
    apply hdb z
    have hd := mfderiv_comp z
      ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) V).mdifferentiable
        (by simp) (b z))
      (hs.mdifferentiable (by simp) z)
    have h := congrArg (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1))
      (Subtype.val : V → Q) (b z)) hvw
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hd] at h
    exact h
  · intro z
    change positiveConeRadialPotential hc (f (unitSlicePreimage hc f hunit z)) = 1 / 2
    rw [apply_unitSlicePreimage hc f hunit]
    dsimp [positiveConeRadialPotential, unitSlicePositiveInclusion]
    rw [z.property]
    norm_num

end Poincare.AncientVolume.ScalarRatio
