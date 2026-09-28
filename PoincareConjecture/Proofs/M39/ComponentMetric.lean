import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import PoincareConjecture.Proofs.M01.NormalizationMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

open Bornology Bundle Manifold
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private abbrev ComponentModel := EuclideanSpace ℝ (Fin 3)

private noncomputable def m39ComponentForm
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier) (x : C.carrier.carrier) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ :=
  ((mfderiv (𝓡 3) (𝓡 3) C.inclusion x).precomp ℝ).comp
    ((g.inner (C.inclusion x)).comp (mfderiv (𝓡 3) (𝓡 3) C.inclusion x))

private theorem m39ComponentDerivative_injective
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (x : C.carrier.carrier) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) C.inclusion x) := by
  have hinv : MDifferentiableAt (𝓡 3) (𝓡 3) C.inverse (C.inclusion x) :=
    ((C.inverse_smooth (C.inclusion x) ⟨x, rfl⟩).contMDiffAt
      (C.inclusion_openEmbedding.isOpen_range.mem_nhds ⟨x, rfl⟩)).mdifferentiableAt
      (by simp)
  have hcomp := mfderiv_comp x hinv
    (C.inclusion_smooth.mdifferentiable (by simp) x)
  have heq : C.inverse ∘ C.inclusion = id := funext C.left_inverse
  rw [heq, mfderiv_id] at hcomp
  intro v w hvw
  have h := congrArg (fun L => L v) hcomp
  have h' := congrArg (fun L => L w) hcomp
  change v = mfderiv (𝓡 3) (𝓡 3) C.inverse (C.inclusion x)
    (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v) at h
  change w = mfderiv (𝓡 3) (𝓡 3) C.inverse (C.inclusion x)
    (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) at h'
  rw [hvw] at h
  exact h.trans h'.symm

private theorem m39ComponentForm_smooth
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier) :
    ContMDiff (𝓡 3)
      ((𝓡 3).prod 𝓘(ℝ, ComponentModel →L[ℝ] ComponentModel →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (ComponentModel →L[ℝ] ComponentModel →L[ℝ] ℝ)
        x (m39ComponentForm C g x)) := by
  intro x₀
  rw [contMDiffAt_section]
  let d := inTangentCoordinates (𝓡 3) (𝓡 3) id C.inclusion
    (mfderiv (𝓡 3) (𝓡 3) C.inclusion) x₀
  let b := fun x : C.carrier.carrier =>
    ContinuousLinearMap.inCoordinates ComponentModel (TangentSpace (𝓡 3))
      (ComponentModel →L[ℝ] ℝ)
      (fun y : A.carrier => TangentSpace (𝓡 3) y →L[ℝ] ℝ)
      (C.inclusion x₀) (C.inclusion x) (C.inclusion x₀) (C.inclusion x)
      (g.inner (C.inclusion x))
  have hd : ContMDiffAt (𝓡 3) 𝓘(ℝ, ComponentModel →L[ℝ] ComponentModel) ∞ d x₀ :=
    C.inclusion_smooth.contMDiffAt.mfderiv_const (by simp)
  have hb : ContMDiffAt (𝓡 3)
      𝓘(ℝ, ComponentModel →L[ℝ] ComponentModel →L[ℝ] ℝ) ∞ b x₀ := by
    have hg := (contMDiffAt_hom_bundle _).mp (g.contMDiff (C.inclusion x₀))
    exact hg.2.comp x₀ C.inclusion_smooth.contMDiffAt
  apply ((hd.clm_precomp (F₃ := ℝ)).clm_comp (hb.clm_comp hd)).congr_of_eventuallyEq
  have hsource := (trivializationAt ComponentModel
    (TangentSpace (𝓡 3) : C.carrier.carrier → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ComponentModel (TangentSpace (𝓡 3)) x₀)
  have htarget := C.inclusion_smooth.continuous.continuousAt.preimage_mem_nhds
    ((trivializationAt ComponentModel
      (TangentSpace (𝓡 3) : A.carrier → Type _) (C.inclusion x₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ComponentModel (TangentSpace (𝓡 3))
          (C.inclusion x₀)))
  filter_upwards [hsource, htarget] with x hx hy
  change C.inclusion x ∈ (trivializationAt ComponentModel
    (TangentSpace (𝓡 3) : A.carrier → Type _) (C.inclusion x₀)).baseSet at hy
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hx hx (Set.mem_univ x)]
  simp only [m39ComponentForm, ContinuousLinearMap.comp_apply]
  change (trivializationAt ℝ (Bundle.Trivial C.carrier.carrier ℝ) x₀).linearMapAt ℝ x
      (g.inner (C.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x
          ((trivializationAt ComponentModel (TangentSpace (𝓡 3)) x₀).symm x v))
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x
          ((trivializationAt ComponentModel (TangentSpace (𝓡 3)) x₀).symm x w))) =
    b x (d x v) (d x w)
  dsimp [b]
  rw [inCoordinates_apply_eq₂ hy hy (Set.mem_univ (C.inclusion x))]
  simp only [d, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  simp only [Bundle.Trivial.eq_trivialization,
    Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply, Function.id_def]
  simp only [← Trivialization.symmL_apply (R := ℝ) _ hy,
    Trivialization.symmL_continuousLinearMapAt (R := ℝ) _ hy,
    Trivialization.symmL_apply (R := ℝ) _ hx]

theorem m39ComponentMetric
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier) :
    Nonempty {gC : RiemannianMetric 3 C.carrier.carrier //
      ∀ x v w, g.inner (C.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = gC.inner x v w} := by
  have hpos (x : C.carrier.carrier) (v : TangentSpace (𝓡 3) x) (hv : v ≠ 0) :
      0 < m39ComponentForm C g x v v := by
    apply g.pos
    intro hz
    exact hv (m39ComponentDerivative_injective C x (by simpa using hz))
  refine ⟨⟨{
    inner := m39ComponentForm C g
    symm := fun x v w => g.symm (C.inclusion x) _ _
    pos := hpos
    isVonNBounded := fun x => m01_isVonNBounded_of_posDef
      (F := ComponentModel) (m39ComponentForm C g x) (hpos x)
    contMDiff := m39ComponentForm_smooth C g
  }, fun _ _ _ => rfl⟩⟩

end PoincareConjecture
