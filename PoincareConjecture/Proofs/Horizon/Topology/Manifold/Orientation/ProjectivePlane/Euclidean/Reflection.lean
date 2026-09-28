import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Homology.SphereReflection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Homology.RelativeBoundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Homology.PuncturedEuclidean
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomologyOpenMap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Euclidean.PositiveLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set Metric

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

theorem sphereReflection_homology_neg (n : Nat) [Fact (Module.finrank Real E = n + 1)]
    (p : sphere (0 : E) 1) (k : Nat) :
    homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (sphereIsometryMap (poleReflection p)))) (k + 1) =
        -𝟙 (integralHomology (sphere (0 : E) 1) (k + 1)) := by
  let A : Set (sphere (0 : E) 1) := {p}ᶜ
  let B : Set (sphere (0 : E) 1) := {-p}ᶜ
  obtain ⟨a, _⟩ := exists_sphere_puncture_homeomorph n p
  obtain ⟨b, _⟩ := exists_sphere_puncture_homeomorph n (-p)
  let : ContractibleSpace A := a.contractibleSpace
  let : ContractibleSpace B := b.contractibleSpace
  have hcover : A ∪ B = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x = p
    · right
      change x ≠ -p
      simpa only [hx] using ne_neg_of_mem_unit_sphere Real p
    · exact Or.inl hx
  apply openCoverSwap_homology_neg A B isOpen_compl_singleton isOpen_compl_singleton
    hcover (sphereIsometryMap (poleReflection p)) (poleReflection_mapsTo p)
      (poleReflection_mapsTo_reverse p) k
  obtain ⟨H⟩ := sphereReflection_overlap_homotopic p
  let H' : TopCat.Homotopy (𝟙 (TopCat.of (↥(A ∩ B))))
      (TopCat.ofHom (coverIntersectionMap A B (sphereIsometryMap (poleReflection p))
        (poleReflection_mapsTo p) (poleReflection_mapsTo_reverse p))) := H
  simpa only [CategoryTheory.Functor.map_id, homologyMap_id] using
    (H'.congr_homologyMap_singularChainComplexFunctor integralCoefficient k).symm

omit [FiniteDimensional Real E] in

theorem linearIsometry_puncture (R : E ≃ₗᵢ[Real] E) :
    MapsTo (⟨R, R.continuous⟩ : C(E, E)) ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
  intro x hx h
  exact hx (R.injective (h.trans R.map_zero.symm))

omit [FiniteDimensional Real E] in

theorem radialHomology_naturality (R : E ≃ₗᵢ[Real] E) (k : Nat) :
    homologyMap (integralChainsFunctor.map (TopCat.ofHom
      (pairSubspaceMap (⟨R, R.continuous⟩ : C(E, E)) (linearIsometry_puncture R)))) k ≫
        (integralHomologyIsoOfHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) k).hom =
      (integralHomologyIsoOfHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) k).hom ≫
        homologyMap (integralChainsFunctor.map (TopCat.ofHom (sphereIsometryMap R))) k := by
  change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
  rw [← homologyMap_comp, ← homologyMap_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 2
  ext x
  change ‖R x.val‖⁻¹ • R x.val = R (‖x.val‖⁻¹ • x.val)
  rw [R.norm_map, map_smul]

theorem reflection_relativeHomologyMap
    (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    homologyMap (integralRelativeMap
      (⟨poleReflection p, (poleReflection p).continuous⟩ :
        C(EuclideanSpace Real (Fin 3), EuclideanSpace Real (Fin 3)))
      (linearIsometry_puncture (poleReflection p))) 3 =
        -𝟙 (integralRelativeHomology ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) 3) := by
  let E := EuclideanSpace Real (Fin 3)
  let R := poleReflection p
  let f : C(E, E) := ⟨R, R.continuous⟩
  let : Fact (Module.finrank Real E = 2 + 1) := ⟨by simp [E]⟩
  have hS := sphereReflection_homology_neg 2 p 1
  have hP : homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (pairSubspaceMap f (linearIsometry_puncture R)))) 2 =
        -𝟙 (integralHomology ({0}ᶜ : Set E) 2) := by
    let e := integralHomologyIsoOfHomotopyEquiv (puncturedSpaceSphereHomotopyEquiv E) 2
    apply (cancel_mono e.hom).mp
    rw [radialHomology_naturality R 2, hS]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id, Category.id_comp]
    simp [e, E]
  let : IsIso (integralRelativeBoundary ({0}ᶜ : Set E) 2) :=
    integralRelativeBoundary_isIso _ 1
  apply (cancel_mono (integralRelativeBoundary ({0}ᶜ : Set E) 2)).mp
  rw [integralRelativeBoundary_naturality, hP]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id, Category.id_comp]

theorem neg_relativeHomologyMap :
    homologyMap (integralRelativeMap
      (⟨ContinuousLinearEquiv.neg Real,
        (ContinuousLinearEquiv.neg Real).continuous⟩ :
        C(EuclideanSpace Real (Fin 3), EuclideanSpace Real (Fin 3)))
      (by
        intro x hx h
        exact hx (by simpa using h))) 3 =
      -𝟙 (integralRelativeHomology
        ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))) 3) := by
  let E := EuclideanSpace Real (Fin 3)
  let N : E ≃L[Real] E := ContinuousLinearEquiv.neg Real
  let p : sphere (0 : E) 1 :=
    Classical.choice (NormedSpace.sphere_nonempty.mpr
      (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
  let R : E ≃ₗᵢ[Real] E := poleReflection p
  let L : E ≃L[Real] E := R.toContinuousLinearEquiv.trans N
  let : Fact (Module.finrank Real E = 2 + 1) := ⟨by
    simp [E, finrank_euclideanSpace]⟩
  have hp : p.val ≠ 0 := by
    exact ne_of_mem_sphere p.property one_ne_zero
  have hRdet : R.toLinearEquiv.toLinearMap.det = -1 := by
    change LinearMap.det (Real ∙ p.val)ᗮ.reflection.toLinearMap = -1
    rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hp]
    norm_num
  have hNmap : N.toLinearEquiv.toLinearMap =
      (-1 : Real) • (LinearMap.id : E →ₗ[Real] E) := by
    ext x
    simp [N]
  have hNdet : N.toLinearEquiv.toLinearMap.det = -1 := by
    rw [hNmap, LinearMap.det_smul, LinearMap.det_id]
    norm_num [E, finrank_euclideanSpace]
  have hLdet : 0 < L.toLinearEquiv.toLinearMap.det := by
    change 0 < (N.toLinearEquiv.toLinearMap.comp R.toLinearEquiv.toLinearMap).det
    rw [LinearMap.det_comp, hNdet, hRdet]
    norm_num
  let fR : C(E, E) := ⟨R, R.continuous⟩
  let fL : C(E, E) := ⟨L, L.continuous⟩
  let fN : C(E, E) := ⟨N, N.continuous⟩
  have hRpun : MapsTo fR ({0}ᶜ : Set E) ({0}ᶜ : Set E) :=
    linearIsometry_puncture R
  have hLpun : MapsTo fL ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
    intro x hx h
    exact hx (L.injective (h.trans L.map_zero.symm))
  have hNpun : MapsTo fN ({0}ᶜ : Set E) ({0}ᶜ : Set E) := by
    intro x hx h
    exact hx (N.injective (h.trans N.map_zero.symm))
  have hcomp : integralRelativeMap fR hRpun ≫ integralRelativeMap fL hLpun =
      integralRelativeMap fN hNpun := by
    rw [integralRelativeMap_comp]
    congr 1
    ext x : 1
    change N (R (R x)) = N x
    simp [R, poleReflection, Submodule.reflection_reflection]
  have hR := reflection_relativeHomologyMap p
  have hL := positiveLinear_relativeHomologyMap L hLdet 3
  have hN := congrArg (fun k => homologyMap k 3) hcomp
  rw [homologyMap_comp, hR, hL] at hN
  simpa [fN, N] using hN.symm

end Poincare.Topology.Orientation.ProjectivePlane
