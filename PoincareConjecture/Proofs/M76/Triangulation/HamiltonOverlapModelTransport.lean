import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOverlapAssembly
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem locallyPiecewiseAffineOn_affine_conjugate
    (L : E ≃ᴬ[ℝ] F) {f : E → E} {U : Set E}
    (hf : LocallyPiecewiseAffineOn f U) :
    LocallyPiecewiseAffineOn (fun y => L (f (L.symm y))) (L.symm ⁻¹' U) := by
  have hi := locallyPiecewiseAffineOn_affine L.symm.toContinuousAffineMap isOpen_univ
  have ho := locallyPiecewiseAffineOn_affine L.toContinuousAffineMap isOpen_univ
  have h := ho.comp (hf.comp hi)
  simpa only [preimage_univ, inter_univ, univ_inter, Function.comp_def,
    ContinuousAffineEquiv.coe_toContinuousAffineMap] using h

theorem exists_covered_straightening_affine_transport
    {X ι : Type*} [TopologicalSpace X]
    (L : E ≃ᴬ[ℝ] F) (c : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid E)
    (hcover : (⋃ i, (c i).source) = univ)
    (d : OpenPartialHomeomorph X E) (hd : d.source = univ)
    (Q : Set X) (hQ : IsCompact Q)
    (hcovered : ∀ (a : ι → OpenPartialHomeomorph X F),
      (∀ i j, (a i).symm.trans (a j) ∈ piecewiseAffineGroupoid F) →
      (⋃ i, (a i).source) = univ →
      ∀ (b : OpenPartialHomeomorph X F), b.source = univ →
      ∀ K : Set X, IsCompact K →
      ∃ (G : X ≃ₜ X) (U S : Set X), IsOpen U ∧ IsCompact S ∧
        EqOn G id Sᶜ ∧ K ⊆ U ∧
        ∀ i, LocallyPiecewiseAffineOn ((b ∘ G) ∘ (a i).symm)
          ((a i).target ∩ (a i).symm ⁻¹' U)) :
    ∃ (G : X ≃ₜ X) (U S : Set X), IsOpen U ∧ IsCompact S ∧
      EqOn G id Sᶜ ∧ Q ⊆ U ∧
      ∀ i, LocallyPiecewiseAffineOn ((d ∘ G) ∘ (c i).symm)
        ((c i).target ∩ (c i).symm ⁻¹' U) := by
  let a : ι → OpenPartialHomeomorph X F := fun i => (c i).transHomeomorph L.toHomeomorph
  let b : OpenPartialHomeomorph X F := d.transHomeomorph L.toHomeomorph
  have hac : ∀ i j, (a i).symm.trans (a j) ∈ piecewiseAffineGroupoid F := by
    intro i j
    obtain ⟨hij, hji⟩ := (mem_piecewiseAffineGroupoid_iff E _).mp (hcompat i j)
    apply (mem_piecewiseAffineGroupoid_iff F _).mpr
    constructor
    · change LocallyPiecewiseAffineOn
        (fun y => L ((c j) ((c i).symm (L.symm y))))
        (L.symm ⁻¹' ((c i).symm.trans (c j)).source)
      exact locallyPiecewiseAffineOn_affine_conjugate L hij
    · change LocallyPiecewiseAffineOn
        (fun y => L ((c i) ((c j).symm (L.symm y))))
        (L.symm ⁻¹' ((c i).symm.trans (c j)).target)
      exact locallyPiecewiseAffineOn_affine_conjugate L hji
  obtain ⟨G, U, S, hU, hS, hfix, hQU, hpl⟩ :=
    hcovered a hac hcover b hd Q hQ
  refine ⟨G, U, S, hU, hS, hfix, hQU, ?_⟩
  intro i
  have hback := locallyPiecewiseAffineOn_affine_conjugate L.symm (hpl i)
  change LocallyPiecewiseAffineOn
    (fun x => L.symm (L (d (G ((c i).symm (L.symm (L x)))))))
    {x | L.symm (L x) ∈ (c i).target ∧ (c i).symm (L.symm (L x)) ∈ U} at hback
  simpa only [L.symm_apply_apply, Function.comp_def, Set.preimage, Set.inter_def,
    Set.mem_ofPred_eq] using hback

end PoincareConjecture.M76
