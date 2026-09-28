import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthSlice
import PoincareConjecture.Proofs.M47.CanonicalNeckPartialIsometry
import PoincareConjecture.Proofs.M47.CanonicalNeckOpenSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_source_initial_birth_identification
    {C X : GeneralizedSliceCarrier.{u}}
    (U : TopologicalSpace.Opens C.carrier) (V : TopologicalSpace.Opens X.carrier)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier X.carrier ∞)
    (hsource : D.source = (U : Set C.carrier))
    (htarget : (V : Set X.carrier) ⊆ D.target)
    (g : RiemannianMetric 3 C.carrier) (h : RiemannianMetric 3 X.carrier)
    (hDmetric : ∀ x ∈ D.source, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x v)
        (mfderiv (𝓡 3) (𝓡 3) D x w) = g.inner x v w)
    (gU : RiemannianMetric 3 U) (hV : RiemannianMetric 3 V) (Q : ℝ)
    (hUmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      gU.inner x v w = Q * g.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (hVmetric : ∀ x : V, ∀ v w : TangentSpace (𝓡 3) x,
      hV.inner x v w = Q * h.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → X.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → X.carrier) x w))
    (oldCenter : U) (recentCenter : V) (hcenter : D oldCenter.val = recentCenter.val) :
    ∃ identify : V → U,
      (∀ x : V, (identify x).val = D.symm x.val) ∧
      ContMDiff (𝓡 3) (𝓡 3) ∞ identify ∧ Function.Injective identify ∧
      identify recentCenter = oldCenter ∧
      ∀ x : V, ∀ v w : TangentSpace (𝓡 3) x,
        gU.inner (identify x) (mfderiv (𝓡 3) (𝓡 3) identify x v)
          (mfderiv (𝓡 3) (𝓡 3) identify x w) = hV.inner x v w := by
  let identify : V → U := fun x => ⟨D.symm x.val, by
    exact (congrArg (fun W : Set C.carrier => D.symm x.val ∈ W) hsource).mp
      (D.map_target (htarget x.property))⟩
  have hmap : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : V => D.symm x.val) := by
    intro x
    exact (D.symm.contMDiffOn.contMDiffAt
      (D.open_target.mem_nhds (htarget x.property))).comp x (contMDiff_subtype_val x)
  have hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ identify := by
    intro x
    apply (ContMDiffAt.subtypeVal_comp_iff U identify x).mp
    exact hmap x
  have hinj : Function.Injective identify := by
    intro x y hxy
    apply Subtype.ext
    exact D.symm.injOn (htarget x.property) (htarget y.property)
      (congrArg Subtype.val hxy)
  have hcenter' : identify recentCenter = oldCenter := by
    apply Subtype.ext
    change D.symm recentCenter.val = oldCenter.val
    rw [← hcenter]
    exact D.left_inv (hsource.symm ▸ oldCenter.property)
  refine ⟨identify, fun _ => rfl, hsmooth, hinj, hcenter', ?_⟩
  intro x v w
  have hsubU : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : U → C.carrier) (identify x) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hsubV : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : V → X.carrier) x :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hDd := (D.symm.contMDiffOn.contMDiffAt
    (D.open_target.mem_nhds (htarget x.property))).mdifferentiableAt (by simp)
  have hId := hsmooth.mdifferentiableAt (by simp) (x := x)
  have hderiv : (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (identify x)).comp
      (mfderiv (𝓡 3) (𝓡 3) identify x) =
      (mfderiv (𝓡 3) (𝓡 3) D.symm x.val).comp
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → X.carrier) x) := by
    rw [← mfderiv_comp x hsubU hId, ← mfderiv_comp x hDd hsubV]
    rfl
  have hv := congrArg (fun L => L v) hderiv
  have hw := congrArg (fun L => L w) hderiv
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [hUmetric, hv, hw, hVmetric]
  apply congrArg (Q * ·)
  exact (partialIsometry_metric_symm D
    (fun y hy a b => (hDmetric y hy a b).symm) x.val (htarget x.property)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → X.carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → X.carrier) x w)).symm

end PoincareConjecture.M47
