import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SphereCylinderPunctures
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereProductFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition










set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "B" => frontier (halfBall 1)
local notation "I" => Icc (0 : ℝ) 1

private theorem exists_halfBall_sphere_product_coordinates :
    ∃ Q : (B ×ˢ I : Set (P3 × ℝ)) ≃ₜ SphereCylinder.carrier,
      Q.IsFinitePL ∧ ∀ x, (Q x : V3 × ℝ).2 = (x : P3 × ℝ).2 := by
  have hpair : IsFinitePLBallPair P3 (halfBall 1) B := by
    rw [frontier_halfBall (Or.inl rfl)]
    exact isFinitePLBallPair_halfBall (Or.inl rfl)
  obtain ⟨C, hC, hCb⟩ := hpair.exists_cube_chart
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] V3)
  have hm (x : halfBall 1) : (x : P3) ∈ B ↔ (C x : V3) ∈ Sphere := by
    simpa only [frontier_closedBall _ one_ne_zero] using hCb x
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  let D := C.restrictSubsets hpair.1 sphere_subset_closedBall hm
  have hD : D.IsFinitePL := hC.restrictSubsets_of_target
    hpair.1 sphere_subset_closedBall hm K hK hKs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hI : (Homeomorph.refl I).IsFinitePL :=
    ⟨id, ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,
      fun _ => rfl⟩
  exact ⟨_, hD.prod hI, fun _ => rfl⟩



theorem original_sphere_cylinder_frontier
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X}
    (H : U ≃ₜ SphereCylinder.carrier) (σ : V3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ SphereCylinder.carrier)
    (hσval : ∀ z : SphereCylinder.carrier, σ z = (H.symm z : X)) :
    IsCompact U ∧ ∀ x : U, (x : X) ∈ frontier U ↔
      (H x : V3 × ℝ).2 ∈ ({0, 1} : Set ℝ) := by
  obtain ⟨Q, hQ, ht⟩ := exists_halfBall_sphere_product_coordinates
  obtain ⟨q, hq, hqval⟩ := hQ
  obtain ⟨K, hK, hKs, hfaces⟩ := hq
  have hq' : FinitePiecewiseAffineOn q K.space := ⟨K, hK, rfl, hfaces⟩
  have hmaps : MapsTo q K.space SphereCylinder.carrier := by
    intro x hx
    rw [← hqval ⟨x, hKs.subset hx⟩]
    exact (Q ⟨x, hKs.subset hx⟩).property
  have hs : PolyhedralPLInCharts e (σ ∘ q) (B ×ˢ I) :=
    hKs ▸ hσ.comp_finitePiecewiseAffineOn K hK hq' hmaps
  let H0 := H.trans Q.symm
  have hval (z : (B ×ˢ I : Set (P3 × ℝ))) : (σ ∘ q) z = (H0.symm z : X) := by
    change σ (q z) = (H.symm (Q z) : X)
    rw [← hqval z, hσval]
  obtain ⟨hU, hi, _⟩ := original_sphere_product_frontier H0 (σ ∘ q) hs hval
  refine ⟨hU, ?_⟩
  intro x
  have hσx : (σ ∘ q) (H0 x) = (x : X) :=
    (hval _).trans (congrArg Subtype.val (H0.symm_apply_apply x))
  have htime : (H0 x : P3 × ℝ).2 = (H x : V3 × ℝ).2 := by
    have ht' := ht (Q.symm (H x))
    rw [Q.apply_symm_apply] at ht'
    exact ht'.symm
  have hin := hi (H0 x)
  rw [hσx, htime] at hin
  rw [frontier, hU.isClosed.closure_eq]
  simp only [mem_sdiff, x.property, true_and, hin, mem_insert_iff, mem_singleton_iff]
  have hbounds := (H x).property.2
  constructor
  · intro hn
    rcases le_or_gt (H x : V3 × ℝ).2 0 with h | h
    · exact Or.inl (le_antisymm h hbounds.1)
    · exact Or.inr (le_antisymm hbounds.2 (le_of_not_gt (fun h' => hn ⟨h, h'⟩)))
  · rintro (h | h) <;> rw [h] <;> norm_num



theorem hasPuncturedSphereModel_of_original_sphere_cylinder
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {U : Set X} {M : Set E}
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (G : U ≃ₜ M) (hG : ∀ x : U, (G x : E) = F x)
    (H : U ≃ₜ SphereCylinder.carrier) (σ : V3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ SphereCylinder.carrier)
    (hσval : ∀ z : SphereCylinder.carrier, σ z = (H.symm z : X)) :
    HasPuncturedSphereModel e F U := by
  obtain ⟨A, r, C, hA, hAS, hdis, ho, hC, hmark⟩ :=
    SphereCylinder.exists_marked_punctured_sphere_model
  have htri := hC
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := htri
  have hcomp : FinitePiecewiseAffineOn (F ∘ σ) SphereCylinder.carrier :=
    hKs ▸ (hKs.symm ▸ hσ).finitePiecewiseAffineOn_comp K hK hF
  let V := H.symm.trans G
  have hV : V.IsFinitePL := by
    refine ⟨F ∘ σ, hcomp, ?_⟩
    intro z
    exact (hG (H.symm z)).trans (congrArg F (hσval z).symm)
  refine HasPuncturedSphereModel.of_marked_model A r hA hAS hdis ho hF G hG
    (V.symm.trans C) (hV.symm.trans hC) ?_
  intro x
  have hv : V.symm (G x) = H x := by
    change H (G.symm (G x)) = H x
    rw [G.symm_apply_apply]
  change (x : X) ∈ frontier U ↔ (C (V.symm (G x)) : Fin 4 → ℝ) ∈ ⋃ b, r b
  rw [hv, ← hmark]
  exact (original_sphere_cylinder_frontier H σ hσ hσval).2 x

end PoincareConjecture.M76
