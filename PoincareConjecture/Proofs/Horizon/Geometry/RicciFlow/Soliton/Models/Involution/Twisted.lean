import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.ProjectivePlane
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.Polar







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Poincare.Topology

noncomputable section

universe u

namespace PoincareConjecture

def twistedProjectivePuncture : RealProjectiveThree :=
  Quotient.mk' (spherePolarPole 2)

theorem spherePolarDomain_projective (x : UnitThreeSphere) :
    x ∈ spherePolarDomain 2 ↔ Quotient.mk' x ≠ twistedProjectivePuncture := by
  change spherePolarTail x ≠ 0 ↔ _
  apply not_congr
  rw [spherePolarTail_eq_zero_iff (n := 2)]
  exact (@Quotient.eq UnitThreeSphere realProjectiveThreeSetoid x
    (spherePolarPole 2)).symm

def twistedProjectiveMap (x : RoundCylinderSpace) :
    PuncturedRealProjectiveThree twistedProjectivePuncture :=
  ⟨Quotient.mk' (spherePolarMap x),
    (spherePolarDomain_projective _).mp (spherePolarMap_mem x)⟩

theorem twistedProjectiveMap_isOpenQuotientMap :
    IsOpenQuotientMap twistedProjectiveMap := by
  let s : Set RealProjectiveThree := {y | y ≠ twistedProjectivePuncture}
  have heq : (spherePolarDomain 2 : Set UnitThreeSphere) =
      (@Quotient.mk' UnitThreeSphere realProjectiveThreeSetoid) ⁻¹' s := by
    ext x
    exact spherePolarDomain_projective x
  have hq : IsOpenQuotientMap (@Quotient.mk' UnitThreeSphere realProjectiveThreeSetoid) :=
    Poincare.Topology.isOpenQuotientMap_of_pair_fibers realProjectiveThreeSetoid
      Neg.neg continuous_neg (fun _ _ => Iff.rfl)
  have ho : IsOpen ((@Quotient.mk' UnitThreeSphere realProjectiveThreeSetoid) ⁻¹' s) := by
    rw [← heq]
    exact (spherePolarDomain 2).isOpen
  exact (hq.restrictPreimage_of_isOpen_preimage s ho).comp
    ((Homeomorph.setCongr heq).isOpenQuotientMap.comp
      (spherePolarHomeomorph 2).isOpenQuotientMap)

theorem twistedProjectiveMap_fibers (x y : RoundCylinderSpace) :
    twistedProjectiveMap x = twistedProjectiveMap y ↔
      x = y ∨ x = (-y.1, -y.2) := by
  rw [Subtype.ext_iff]
  change Quotient.mk realProjectiveThreeSetoid (spherePolarMap x) =
    Quotient.mk realProjectiveThreeSetoid (spherePolarMap y) ↔ _
  rw [Quotient.eq]
  change spherePolarMap x = spherePolarMap y ∨
    spherePolarMap x = -spherePolarMap y ↔ _
  have hi : Function.Injective (spherePolarMap : RoundCylinderSpace → UnitThreeSphere) := by
    intro a b h
    apply (spherePolarHomeomorph 2).injective
    exact Subtype.ext h
  rw [← spherePolarMap_neg, hi.eq_iff, hi.eq_iff]

def cylinderCenterShift (c : ℝ) :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun x := (x.1, x.2 - c)
  invFun x := (x.1, x.2 + c)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)

namespace SphereLineProductData

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]

def centeredCylinderDiffeomorph (d : SphereLineProductData (P := P)) (c : ℝ) :
    letI := d.surface_topology
    letI := d.surface_charted
    letI := d.surface_manifold
    letI := d.product_charted
    letI := d.product_manifold
    Diffeomorph (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (d.surface × ℝ) RoundCylinderSpace ∞ := by
  letI := d.surface_topology
  letI := d.surface_charted
  letI := d.surface_manifold
  letI := d.product_charted
  letI := d.product_manifold
  exact
    { toFun := fun x => (d.surface_sphere x.1, x.2 - c)
      invFun := fun x => (d.surface_sphere.symm x.1, x.2 + c)
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp
      contMDiff_toFun := ((cylinderCenterShift c).contMDiff.comp
        (d.surface_sphere.contMDiff.prodMap contMDiff_id)).comp
          d.product_smooth_to_canonical
      contMDiff_invFun := d.product_smooth_from_canonical.comp
        ((d.surface_sphere.symm.contMDiff.prodMap contMDiff_id).comp
          (cylinderCenterShift c).symm.contMDiff) }

end SphereLineProductData

namespace QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem exists_twistedProjectiveCoordinates (q : QuotientSphereLineCertificate G)
    (c : ℝ) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    letI := q.quotient_topology
    letI := q.quotient_charted
    letI := q.quotient_manifold
    (∀ x : q.product.surface × ℝ,
      q.involution x = (q.product.surface_sphere.symm (-(q.product.surface_sphere x.1)),
        2 * c - x.2)) →
    ∃ e : q.quotient_carrier ≃ₜ PuncturedRealProjectiveThree twistedProjectivePuncture,
      ∀ x : q.product.surface × ℝ,
        e (q.quotient_map x) = twistedProjectiveMap (q.product.centeredCylinderDiffeomorph c x) := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  letI := q.quotient_topology
  letI := q.quotient_charted
  letI := q.quotient_manifold
  intro hformula
  let E := q.product.centeredCylinderDiffeomorph c
  have hequiv (x : q.product.surface × ℝ) :
      E (q.involution x) = (-(E x).1, -(E x).2) := by
    rw [hformula x]
    apply Prod.ext
    · exact q.product.surface_sphere.apply_symm_apply _
    · change 2 * c - x.2 - c = -(x.2 - c)
      ring
  let f : C(q.product.surface × ℝ, q.quotient_carrier) :=
    ⟨q.quotient_map, q.quotient_map_smooth.continuous⟩
  let k : C(q.product.surface × ℝ,
      PuncturedRealProjectiveThree twistedProjectivePuncture) :=
    ⟨twistedProjectiveMap ∘ E,
      twistedProjectiveMap_isOpenQuotientMap.continuous.comp E.continuous⟩
  have hk : IsOpenQuotientMap k :=
    twistedProjectiveMap_isOpenQuotientMap.comp E.toHomeomorph.isOpenQuotientMap
  have hf : Topology.IsQuotientMap f := q.quotient_map_isOpenQuotientMap.isQuotientMap
  have hfib : ∀ x y, f x = f y ↔ k x = k y := by
    intro x y
    change q.quotient_map x = q.quotient_map y ↔
      twistedProjectiveMap (E x) = twistedProjectiveMap (E y)
    rw [q.quotient_fiber_eq_orbit, twistedProjectiveMap_fibers]
    rw [← hequiv y]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (congrArg E (q.involution_involutive x).symm)
    · rintro (h | h)
      · exact Or.inl (E.injective h).symm
      · right
        have h := E.injective h
        rw [h, q.involution_involutive]
  refine ⟨hf.homeomorphOfFibers hk.isQuotientMap hfib, ?_⟩
  intro x
  exact hf.homeomorphOfFibers_apply hk.isQuotientMap hfib x

theorem exists_twistedProjectiveSmoothModel (q : QuotientSphereLineCertificate G)
    (c : ℝ) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    letI := q.quotient_topology
    letI := q.quotient_charted
    letI := q.quotient_manifold
    (∀ x : q.product.surface × ℝ,
      q.involution x = (q.product.surface_sphere.symm (-(q.product.surface_sphere x.1)),
        2 * c - x.2)) →
    ∃ e : q.quotient_carrier ≃ₜ PuncturedRealProjectiveThree twistedProjectivePuncture,
      ∃ C : StandardPuncturedProjectiveCover q.quotient_carrier twistedProjectivePuncture Set.univ,
        ∀ (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ twistedProjectivePuncture),
          e (C.cover x) = ⟨Quotient.mk' x, hx⟩ := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  letI := q.quotient_topology
  letI := q.quotient_charted
  letI := q.quotient_manifold
  intro hformula
  obtain ⟨e, he⟩ := q.exists_twistedProjectiveCoordinates c hformula
  let E := q.product.centeredCylinderDiffeomorph c
  let cover : UnitThreeSphere → q.quotient_carrier :=
    fun x => q.quotient_map (E.symm (spherePolarInverseTotal 2 x))
  have hcoord (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ twistedProjectivePuncture) :
      e (cover x) = ⟨Quotient.mk' x, hx⟩ := by
    have hx' := (spherePolarDomain_projective x).mpr hx
    change e (q.quotient_map (E.symm (spherePolarInverseTotal 2 x))) = _
    rw [he]
    change twistedProjectiveMap (E (E.symm (spherePolarInverseTotal 2 x))) = _
    rw [E.apply_symm_apply]
    apply Subtype.ext
    change Quotient.mk realProjectiveThreeSetoid
      (spherePolarMap (spherePolarInverseTotal 2 x)) = Quotient.mk' x
    have h := spherePolar_right_inv (⟨x, hx'⟩ : spherePolarDomain 2)
    rw [show spherePolarInverseTotal 2 x = spherePolarInverse ⟨x, hx'⟩ by
      exact spherePolarInverseTotal_coe ⟨x, hx'⟩, h]
    rfl
  refine ⟨e, ⟨cover, ?_, ?_, ?_⟩, hcoord⟩
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := Quotient.mk'_surjective (e y).val
    have hp : Quotient.mk' x ≠ twistedProjectivePuncture := by
      rw [hx]
      exact (e y).property
    refine ⟨x, hp, e.injective ?_⟩
    rw [hcoord x hp]
    exact Subtype.ext hx
  · intro x y hx hy
    constructor
    · intro h
      have heq := congrArg e h
      rw [hcoord x hx, hcoord y hy] at heq
      exact Quotient.exact (congrArg Subtype.val heq)
    · intro h
      apply e.injective
      rw [hcoord x hx, hcoord y hy]
      apply Subtype.ext
      exact Quotient.sound h
  · intro x
    have hx := (spherePolarDomain_projective x.val).mpr x.property
    have h₁ := (spherePolarPartialDiffeomorph 2).symm.isLocalDiffeomorphAt
      (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ hx
    have h₂ := h₁.comp (𝓡 3) (q.product.surface × ℝ)
      (E.symm.isLocalDiffeomorph _)
    exact h₂.comp (𝓡 3) q.quotient_carrier (q.quotient_map_localDiffeomorph _)

end QuotientSphereLineCertificate

end PoincareConjecture
