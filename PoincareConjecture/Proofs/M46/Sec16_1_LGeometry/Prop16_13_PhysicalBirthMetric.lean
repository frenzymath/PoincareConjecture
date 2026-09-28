import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BirthMetric
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_PhysicalScalar










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem surgerySlice_pullback_eq_of_identity
    {F : SurgeryFlowData.{u}} {t s : ℝ} {U : Set (F.slice t).carrier}
    (hU : IsOpen U) (hst : s = t)
    (f : (F.slice t).carrier → (F.slice s).carrier)
    (hbase : ∀ y ∈ U, HEq (f y) y)
    {y : (F.slice t).carrier} (hy : y ∈ U) (V W : TangentSpace (𝓡 3) y) :
    (F.metric s).inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y V)
      (mfderiv (𝓡 3) (𝓡 3) f y W) = (F.metric t).inner y V W := by
  subst s
  have hnear : f =ᶠ[𝓝 y] id := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact eq_of_heq (hbase z hz)
  rw [hnear.mfderiv_eq, mfderiv_id]
  change (F.metric t).inner (f y) V W = (F.metric t).inner y V W
  rw [hnear.eq_of_nhds]
  rfl




theorem surgeryCylinder_pullbackInner_zero
    {F : SurgeryFlowData.{u}} {t q : ℝ} {J : Set ℝ}
    {U : Set (F.slice t).carrier} (hU : IsOpen U)
    (e : SurgeryFlowCylinder F (F.slice t) t q J U)
    (hzero : (0 : ℝ) ∈ J) (hbase : ∀ y ∈ U, HEq (e.forward 0 hzero y) y)
    {y : (F.slice t).carrier} (hy : y ∈ U) (V W : TangentSpace (𝓡 3) y) :
    e.pullbackInner 0 hzero y V W = q * (F.metric t).inner y V W := by
  unfold SurgeryFlowCylinder.pullbackInner
  congr 1
  exact surgerySlice_pullback_eq_of_identity hU (by simp) _ hbase hy V W




theorem capComparison_birth_lower_on_physical_ball
    {F : SurgeryFlowData.{u}} {S : MaximalStandardCapFlow F.standard_initial}
    {t : ℝ} {hT : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    {i : Fin (F.event t hT).cap_count} {A eta mu : ℝ} {J : Set ℝ}
    {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J) {s : ℝ} (hs : s ∈ J)
    (hbound : ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ v : StandardCapSpace,
      mu * capComparisonCoefficients e initial.chart 0 hzero x v v ≤
        capComparisonCoefficients e initial.chart s hs x v v)
    {y : (F.slice t).carrier} (hy : y ∈ U) (V : TangentSpace (𝓡 3) y) :
    mu * e.pullbackInner 0 hzero y V V ≤ e.pullbackInner s hs y V V := by
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  obtain ⟨x, hx, rfl⟩ := (himage.symm ▸ hy)
  let f := capInitialPartialDiffeomorph initial
  have hlocal := f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx
  let L := hlocal.mfderivToContinuousLinearEquiv (by simp)
  have hdf : mfderiv (𝓡 3) (𝓡 3) initial.chart x (L.symm V) = V :=
    L.apply_symm_apply V
  have h := hbound x hx (L.symm V)
  rw [capComparisonCoefficients_apply, capComparisonCoefficients_apply, hdf] at h
  exact h

end PoincareConjecture.Proofs.M46
