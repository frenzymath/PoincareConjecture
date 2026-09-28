import PoincareConjecture.Proofs.M38.DeckSphereLifts
import PoincareConjecture.Proofs.M38.SphericalSphereFilling
import PoincareConjecture.Proofs.M38.LiftedSphereDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

theorem exists_surgeryBall_of_finite_spherical_cover
    (Q : GeneralizedSliceCarrier.{u})
    {G : Type*} [Group G] [Finite G] [MulAction G UnitThreeSphere]
    (q : UnitThreeSphere → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hsurj : Function.Surjective q)
    (e : G → Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞)
    (he : ∀ (g : G) (x : UnitThreeSphere), e g x = g • x)
    (hdeck : ∀ (g : G) (x : UnitThreeSphere), q (g • x) = q x)
    (hfree : ∀ (g : G) (x : UnitThreeSphere), g • x = x → g = 1)
    (hfibers : ∀ x y : UnitThreeSphere, q x = q y → ∃ g : G, y = g • x)
    (f : UnitTwoSphere → Q.carrier)
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (p : Q.carrier) (hp : p ∉ range f) :
    ∃ B : SurgeryBallEmbedding Q, frontier B.closedBall = range f := by
  classical
  obtain ⟨L, hL, hqL, hmul, hdisj, _⟩ :=
    exists_equivariant_sphere_lifts q hq hsurj e he hdeck hfree hfibers f hf
  obtain ⟨p₀, hp₀⟩ := hsurj p
  let d : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere sphereCarrier.{u}.carrier ∞ := {
    toEquiv := (Homeomorph.ulift : sphereCarrier.{u}.carrier ≃ₜ UnitThreeSphere).symm.toEquiv
    contMDiff_toFun := threeManifold_up_contMDiff UnitThreeSphere
    contMDiff_invFun := threeManifold_down_contMDiff UnitThreeSphere }
  let F : G → UnitTwoSphere → sphereCarrier.{u}.carrier := fun g => d ∘ L g
  have hF (g : G) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (F g) :=
    (hL g).comp_localDiffeomorph d.isLocalDiffeomorph
      (d.injective.comp (hL g).isEmbedding.injective)
  have hpF (g : G) : d p₀ ∉ range (F g) := by
    rintro ⟨z, hz⟩
    have hz' : L g z = p₀ := d.injective hz
    exact hp ⟨z, (hqL g z).symm.trans (by rw [hz', hp₀])⟩
  choose B hB hpB using fun g => exists_surgerySphereBall_avoiding_point
    (F g) (hF g) (d p₀) (hpF g)
  let E : G → Diffeomorph (𝓡 3) (𝓡 3)
      sphereCarrier.{u}.carrier sphereCarrier.{u}.carrier ∞ :=
    fun g => d.symm.trans ((e g).trans d)
  have hE (g : G) (x : sphereCarrier.{u}.carrier) :
      E g x = d (g • d.symm x) := by
    change d (e g (d.symm x)) = _
    rw [he]
  have hEone (x) : E 1 x = x := by rw [hE, one_smul, d.apply_symm_apply]
  have hEinv (g) : (E g).symm = E g⁻¹ := by
    apply Diffeomorph.ext
    intro x
    apply (E g).injective
    change (E g) ((E g).symm x) = (E g) ((E g⁻¹) x)
    rw [(E g).apply_symm_apply, hE, hE, d.symm_apply_apply, smul_inv_smul,
      d.apply_symm_apply]
  let π : sphereCarrier.{u}.carrier → Q.carrier := q ∘ d.symm
  have hπ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ π :=
    fun x => (d.symm.isLocalDiffeomorph x).comp (𝓡 3) Q.carrier (hq (d.symm x))
  have hπfibers (x y) (hxy : π x = π y) : ∃ g : G, y = E g x := by
    obtain ⟨g, hg⟩ := hfibers (d.symm x) (d.symm y) hxy
    exact ⟨g, by rw [hE, ← hg, d.apply_symm_apply]⟩
  have hboundary (g i : G) : frontier (B (g • i)).closedBall =
      E g '' frontier (B i).closedBall := by
    rw [hB, hB, ← range_comp]
    apply congrArg range
    funext z
    change d (L (g * i) z) = E g (d (L i z))
    rw [hmul, hE, d.symm_apply_apply]
  have hdisjoint (i j : G) (hij : i ≠ j) :
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall) := by
    rw [hB, hB]
    apply disjoint_left.mpr
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    exact disjoint_left.mp (hdisj i j hij) (mem_range_self a)
      ⟨b, d.injective (hb.trans ha.symm)⟩
  obtain ⟨i, D, _, hD⟩ := exists_descended_innermost_sphereBall π hπ E hEone hEinv
    hπfibers (fun g i hi => by
      change g * i = i at hi
      exact mul_right_cancel (hi.trans (one_mul i).symm))
    B hboundary hdisjoint (d p₀) hpB
  refine ⟨D, hD.trans ?_⟩
  rw [hB, ← range_comp]
  apply congrArg range
  funext z
  change q (d.symm (d (L i z))) = f z
  rw [d.symm_apply_apply, hqL]

end PoincareConjecture.M38
