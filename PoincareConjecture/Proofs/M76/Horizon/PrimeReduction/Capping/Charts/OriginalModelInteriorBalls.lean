import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteModelCollarTransport
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FinitePLBallInteriorChart
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_model_interior_ball
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X} {P : Set E}
    (he : PLDomain e R) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f R) (H : R ≃ₜ P) (hH : ∀ x : R, (H x : E) = f x)
    (hU : IsOpen U) {p : X} (hp : p ∈ U ∩ interior R) :
    ∃ A B : Set E, IsFinitePLBallPair V3 A B ∧
      A ⊆ f '' (U ∩ interior R) ∧ A ⊆ P ∧ f p ∈ A \ B ∧
      IsOpen ((Subtype.val : P → E) ⁻¹' (A \ B)) := by
  obtain ⟨i, hpi⟩ := he.cover p
  let Q := e i
  let V := Q.target ∩ Q.symm ⁻¹' (U ∩ interior R)
  have hV : IsOpen V := Q.symm.continuousOn.isOpen_inter_preimage Q.open_target
    (hU.inter isOpen_interior)
  have hpV : Q p ∈ V := by
    refine ⟨Q.mapsTo hpi, ?_⟩
    change Q.symm (Q p) ∈ U ∩ interior R
    rw [Q.left_inv hpi]
    exact hp
  obtain ⟨K, hK, hKcv, hpK, hKV⟩ := hV.exists_finite_convex_neighborhood hpV
  have hKQ : K.space ⊆ Q.target := fun _ hx => (hKV hx).1
  have hKU : MapsTo Q.symm K.space (U ∩ interior R) := fun _ hx => (hKV hx).2
  have hKR : MapsTo Q.symm K.space R := fun _ hx => interior_subset (hKU hx).2
  have hKc := K.isCompact_space_of_finite hK
  have hball : IsFinitePLBallPair V3 K.space (frontier K.space) :=
    isFinitePLBallPair_of_compact_convex hKc hKcv ⟨Q p, hpK⟩ K hK rfl
  have hmap : FinitePiecewiseAffineOn (f ∘ Q.symm) K.space :=
    (hf i).finitePiecewiseAffineOn K hK hKQ
  have hinj : InjOn (f ∘ Q.symm) K.space := by
    intro x hx y hy hxy
    exact Q.symm.injOn (hKQ hx) (hKQ hy) (hfi (hKR hx) (hKR hy) hxy)
  let A := (f ∘ Q.symm) '' K.space
  let B := (f ∘ Q.symm) '' frontier K.space
  have hdiff : A \ B = (f ∘ Q.symm) '' interior K.space := by
    dsimp only [A, B]
    rw [← self_sdiff_frontier K.space]
    simpa only [inter_eq_right.mpr hKc.isClosed.frontier_subset] using
      (Set.InjOn.image_sdiff (t := frontier K.space) hinj).symm
  have hAP : A ⊆ P := by
    rintro _ ⟨x, hx, rfl⟩
    change f (Q.symm x) ∈ P
    exact hH ⟨Q.symm x, hKR hx⟩ ▸ (H ⟨Q.symm x, hKR hx⟩).property
  refine ⟨A, B, hball.image hmap hinj, ?_, hAP, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem f (hKU hx)
  · rw [hdiff]
    refine ⟨Q p, hpK, ?_⟩
    change f (Q.symm (Q p)) = f p
    rw [Q.left_inv hpi]
  · rw [hdiff]
    simp only [Function.comp_def]
    rw [← image_image f Q.symm]
    apply isOpen_relative_model_image H f hH
    · rintro _ ⟨x, hx, rfl⟩
      exact hKR (interior_subset hx)
    · exact (Q.symm.isOpen_image_of_subset_source isOpen_interior
        (interior_subset.trans hKQ)).preimage continuous_subtype_val



theorem exists_original_model_interior_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X} {P : Set E}
    (he : PLDomain e R) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f R) (H : R ≃ₜ P) (hH : ∀ x : R, (H x : E) = f x)
    (hU : IsOpen U) {p : X} (hp : p ∈ U ∩ interior R) :
    ∃ (A B : Set E) (Q : OpenPartialHomeomorph P V3) (a : E → V3) (b : V3 → E),
      IsFinitePLBallPair V3 A B ∧ A ⊆ f '' (U ∩ interior R) ∧ A ⊆ P ∧
      H ⟨p, interior_subset hp.2⟩ ∈ Q.source ∧
      Q.source = (Subtype.val : P → E) ⁻¹' (A \ B) ∧
      Q.target = interior (Metric.closedBall (0 : V3) 1) ∧
      FinitePiecewiseAffineOn a A ∧
      FinitePiecewiseAffineOn b (Metric.closedBall (0 : V3) 1) ∧
      (∀ x : P, Q x = a x) ∧
      (∀ y ∈ Metric.closedBall (0 : V3) 1, (Q.symm y : E) = b y) ∧
      MapsTo b (Metric.closedBall (0 : V3) 1) A ∧
      LeftInvOn b a A ∧ RightInvOn b a (Metric.closedBall (0 : V3) 1) := by
  obtain ⟨A, B, hball, hAU, hAP, hpA, hopen⟩ :=
    exists_original_model_interior_ball he f hf hfi H hH hU hp
  obtain ⟨Q, a, b, hQs, hQt, ha, hb, hQa, hQb, hbA, hba, hab⟩ :=
    hball.exists_open_cube_interior_chart (ContinuousLinearEquiv.refl ℝ V3) hAP hopen
  refine ⟨A, B, Q, a, b, hball, hAU, hAP, ?_, hQs, hQt, ha, hb, hQa, hQb, hbA, hba, hab⟩
  rw [hQs]
  change (H ⟨p, interior_subset hp.2⟩ : E) ∈ A \ B
  rw [hH]
  exact hpA

end PoincareConjecture.M76
