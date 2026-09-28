import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedBallSphereModel
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology









set_option autoImplicit false
open Set Metric Geometry Geometry.CubicalThreeSphere

namespace PoincareConjecture.M76.ChartwisePLBall

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Cube" => closedBall (0 : V3) 1

theorem exists_single_hole_marked_model
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {D bd : Set X}
    (b : ChartwisePLBall e D bd) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f D) :
    ∃ (G : D ≃ₜ (f '' D))
      (C : (f '' D) ≃ₜ (sphere \ (upper \ seam) : Set V4)),
      (∀ x : D, (G x : E) = f x) ∧ C.IsFinitePL ∧
      (∀ x : D, (x : X) ∈ bd ↔ (C (G x) : V4) ∈ seam) ∧
      (∀ x : D, (x : X) ∈ frontier D ↔ (C (G x) : V4) ∈ seam) ∧
      (fun x : D => (C (G x) : V4)) ''
        ((Subtype.val : D → X) ⁻¹' bd) = seam := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 3)
  have hp : PolyhedralPLInCharts e b.map K.space := hKs.symm ▸ b.piecewiseAffine
  have hcomp : FinitePiecewiseAffineOn (f ∘ b.map) Cube := by
    rw [← hKs]
    exact hp.finitePiecewiseAffineOn_comp K hK hf
  have hc : Continuous (fun x : D => f x) := by
    have hc₀ := hcomp.continuousOn.domRestrict.comp b.parametrization.symm.continuous
    convert hc₀ using 1
    funext x
    change f x = f (b.map (b.parametrization.symm x))
    rw [b.map_eq, b.parametrization.apply_symm_apply]
  let : CompactSpace D := isCompact_iff_compactSpace.mp b.isCompact
  let G : D ≃ₜ (f '' D) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f D hfi) (hc.subtype_mk _)
  have hG (x : D) : (G x : E) = f x := rfl
  have hball := b.finitePLBallPair_image subset_rfl f hf hfi
  obtain ⟨H, hH, hHbd⟩ := hball.exists_homeomorph lower_ball
  have htarget : sphere \ (upper \ seam) = lower := by
    rw [← lower_union_upper, ← lower_inter_upper]
    ext x
    simp only [mem_sdiff, mem_union, mem_inter_iff]
    tauto
  let C := H.trans (Homeomorph.setCongr htarget.symm)
  have hC : C.IsFinitePL := hH.setCongr rfl htarget.symm
  have hbd (x : D) : (x : X) ∈ bd ↔ (C (G x) : V4) ∈ seam := by
    have him : f x ∈ f '' bd ↔ (x : X) ∈ bd := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact hfi (b.boundary_subset hy) x.property hyx ▸ hy
      · exact fun hx => ⟨x, hx, rfl⟩
    exact him.symm.trans (hHbd (G x))
  refine ⟨G, C, hG, hC, hbd, ?_, ?_⟩
  · intro x
    rw [b.frontier_eq]
    exact hbd x
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hbd x).mp hx
    · intro y hy
      have hyT : y ∈ sphere \ (upper \ seam) := htarget.symm ▸ lower_ball.1 hy
      let x := G.symm (C.symm ⟨y, hyT⟩)
      have hvalue : (C (G x) : V4) = y := by
        dsimp only [x]
        rw [G.apply_symm_apply, C.apply_symm_apply]
      exact ⟨x, (hbd x).mpr (hvalue.symm ▸ hy), hvalue⟩

theorem hasPuncturedSphereModel
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {D bd : Set X}
    (b : ChartwisePLBall e D bd) (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f D) : HasPuncturedSphereModel e f D := by
  obtain ⟨G, C, hG, hC, _, hmark, _⟩ := b.exists_single_hole_marked_model f hf hfi
  have hopen : IsOpen ((Subtype.val : sphere → V4) ⁻¹' (upper \ seam)) := by
    have heq : (Subtype.val : sphere → V4) ⁻¹' (upper \ seam) =
        ((Subtype.val : sphere → V4) ⁻¹' lower)ᶜ := by
      ext x
      have hx := lower_union_upper.symm.subset x.property
      have hs := Set.ext_iff.mp lower_inter_upper (x : V4)
      simp only [mem_union] at hx
      simp only [mem_inter_iff] at hs
      simp only [mem_preimage, mem_sdiff, mem_compl_iff]
      tauto
    rw [heq]
    exact (lower_ball.isCompact.isClosed.preimage continuous_subtype_val).isOpen_compl
  have htarget : (sphere \ ⋃ _ : Unit, upper \ seam : Set V4) =
      sphere \ (upper \ seam) := by rw [iUnion_const]
  exact HasPuncturedSphereModel.of_marked_model
    (fun _ : Unit => upper) (fun _ : Unit => seam)
    (fun _ => upper_ball) (fun _ => lower_union_upper ▸ subset_union_right)
    (fun i j hij => False.elim (hij (Subsingleton.elim _ _))) (fun _ => hopen)
    hf G hG (C.trans (Homeomorph.setCongr htarget.symm))
    (hC.setCongr rfl htarget.symm) (by
      intro x
      change (x : X) ∈ frontier D ↔ (C (G x) : V4) ∈ ⋃ _ : Unit, seam
      simpa only [iUnion_const] using hmark x)

end PoincareConjecture.M76.ChartwisePLBall
