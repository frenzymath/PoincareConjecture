import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Correction
import PoincareConjecture.Proofs.Horizon.LinearAlgebra.CrossProduct.Cofactor
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

open Poincare.LinearAlgebra

theorem contDiff_cofactorNormal {G : E3 -> E3} (hG : ContDiff Real ∞ G) :
    ContDiff Real ∞ (fun x => euclideanCofactorNormal (fderiv Real G x) x) := by
  have hA (i j : Fin 3) : ContDiff Real ∞
      (fun x => LinearMap.toMatrix' (euclideanCoordinateLinearMap (fderiv Real G x)) i j) := by
    change ContDiff Real ∞ (fun x =>
      (fderiv Real G x (WithLp.toLp 2 (Pi.single j 1))) i)
    exact (contDiff_apply Real Real i).comp
      ((EuclideanSpace.equiv (Fin 3) Real).contDiff.comp
        ((hG.fderiv_right (by simp)).clm_apply contDiff_const))
  apply (EuclideanSpace.equiv (Fin 3) Real).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  change ContDiff Real ∞ (fun x =>
    ((LinearMap.toMatrix' (euclideanCoordinateLinearMap (fderiv Real G x))).adjugate.transpose
      *ᵥ (x : Fin 3 -> Real)) i)
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply ContDiff.sum
  intro j _
  apply ContDiff.mul
  · rw [show (fun x => (LinearMap.toMatrix'
        (euclideanCoordinateLinearMap (fderiv Real G x))).adjugate j i) =
        (fun x => ((LinearMap.toMatrix'
          (euclideanCoordinateLinearMap (fderiv Real G x))).updateRow i (Pi.single j 1)).det)
      from funext fun _ => Matrix.adjugate_apply _ _ _]
    simp only [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    apply ContDiff.mul contDiff_const
    apply contDiff_prod
    intro k _
    by_cases hk : σ k = i
    · simp only [Matrix.updateRow_apply, hk]
      exact contDiff_const
    · simp only [Matrix.updateRow_apply, hk]
      exact hA (σ k) k
  · exact (contDiff_apply Real Real j).comp (EuclideanSpace.equiv (Fin 3) Real).contDiff

theorem exists_nonsingular_sphere_extension
    (f : S2 -> E3) (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ F : E3 -> E3, ContDiff Real ∞ F ∧
      (∀ p : S2, F p = f p) ∧
      ∀ p : S2, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ F p := by
  obtain ⟨G, hG, hrestrict⟩ := exists_contDiff_extension_sphere f hf.contMDiff
  let N : E3 -> E3 := fun x => euclideanCofactorNormal (fderiv Real G x) x
  have hN : ContDiff Real ∞ N := contDiff_cofactorNormal hG
  let F := correctNormal G N
  have hF : ContDiff Real ∞ F := contDiff_correctNormal hG hN
  have hbij (p : S2) : Function.Bijective (fderiv Real F p) := by
    have hp : ‖(p : E3)‖ = 1 := by simp
    have hinj := injective_tangent_add_euclideanCofactorNormal (fderiv Real G p) p
      (by simp)
      (injOn_fderiv_extension_tangent_sphere hf hG hrestrict p)
    have heq : (fderiv Real F p : E3 -> E3) =
        fun v => fderiv Real G p (v - inner Real (p : E3) v • (p : E3)) +
          inner Real (p : E3) v • N p :=
      funext (fderiv_correctNormal hG hN hp)
    have hi : Function.Injective (fderiv Real F p) := heq.symm ▸ hinj
    exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  let U : Set E3 := {x | IsUnit (fderiv Real F x)}
  have hU : IsOpen U := Units.isOpen.preimage (hF.fderiv_right (m := ∞) (by simp)).continuous
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ F U :=
    Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv hU
      hF.contMDiff.contMDiffOn (fun x hx => by
        rw [mfderiv_eq_fderiv]
        exact (ContinuousLinearMap.isUnit_iff_bijective (f := fderiv Real F x)).mp hx)
  refine ⟨F, hF, fun p => (correctNormal_sphere G N (by simp)).trans (hrestrict p), ?_⟩
  intro p
  exact hlocal ⟨p, ContinuousLinearMap.isUnit_iff_bijective.mpr (hbij p)⟩

theorem exists_sphere_neighborhood
    (f : S2 -> E3) (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ e : OpenPartialHomeomorph E3 E3,
      sphere 0 1 ⊆ e.source ∧ range f ⊆ e.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      ∀ p : S2, e p = f p := by
  obtain ⟨F, _, hrestrict, hlocal⟩ := exists_nonsingular_sphere_extension f hf
  have hinj : InjOn F (sphere 0 1) := by
    intro x hx y hy hxy
    have h : f ⟨x, hx⟩ = f ⟨y, hy⟩ :=
      (hrestrict ⟨x, hx⟩).symm.trans (hxy.trans (hrestrict ⟨y, hy⟩))
    exact congrArg Subtype.val (hf.isEmbedding.injective h)
  obtain ⟨e, hs, ht, heq, he, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact
      (isCompact_sphere 0 1) hinj (fun x hx => hlocal ⟨x, hx⟩)
  refine ⟨e, hs, ?_, he, hei, fun p => (heq (hs p.property)).trans (hrestrict p)⟩
  rintro y ⟨p, rfl⟩
  apply ht
  exact ⟨p, p.property, hrestrict p⟩

end Poincare.Manifold.Schoenflies
