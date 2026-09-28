import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.CarrierBallCertificates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.nonempty_image
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}
    (b : ChartwisePLBall e D S) (G : X ≃ₜ X)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hG : ∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) :
    Nonempty (ChartwisePLBall e (G '' D) (G '' S)) := by
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  have hf : PolyhedralPLInCharts e b.map K.space := hKs.symm ▸ b.piecewiseAffine
  refine ⟨{
    boundary_subset := image_mono b.boundary_subset
    parametrization := b.parametrization.trans (G.image D)
    map := G ∘ b.map
    map_eq := ?_
    piecewiseAffine := ?_
    boundary_eq := ?_ }⟩
  · intro x
    change G (b.map x) = G (b.parametrization x)
    rw [b.map_eq]
  · simpa only [hKs] using hf.comp_chart_homeomorph K hK G hcover hG
  · intro x
    change G (b.parametrization x) ∈ G '' S ↔ _
    rw [G.injective.mem_set_image]
    exact b.boundary_eq x

theorem ChartwisePLBall.exists_ball_before_supported_motion
    {X α : Type*} [TopologicalSpace X]
    {atlas : α → OpenPartialHomeomorph X V3} {A D V S : Set X}
    (G : X ≃ₜ X) (b : ChartwisePLBall atlas A (G '' S))
    (hAD : A ⊆ D) (hVD : V ⊆ D) (hfix : EqOn G id Vᶜ)
    (hcover : ∀ x, ∃ i, x ∈ (atlas i).source)
    (hG : ∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
      piecewiseAffineGroupoid V3) :
    ∃ A' : Set X, A' ⊆ D ∧ Nonempty (ChartwisePLBall atlas A' S) := by
  have hball := b.nonempty_image G.symm hcover hG
  rw [image_image] at hball
  have hball' : Nonempty (ChartwisePLBall atlas (G.symm '' A) S) := by
    simpa only [Function.comp_def,G.symm_apply_apply,image_id'] using hball
  refine ⟨G.symm '' A,?_,hball'⟩
  rintro _ ⟨x,hx,rfl⟩
  by_contra hn
  have hfixed : G (G.symm x) = G.symm x := hfix (fun h => hn (hVD h))
  rw [G.apply_symm_apply] at hfixed
  exact hn (hfixed ▸ hAD hx)

theorem exists_ball_of_moved_carrier_ball
    {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A T W D : Set E} (hA : IsFinitePLBallPair V3 A T)
    (hAD : A ⊆ D) (hDW : D ⊆ W)
    (atlas : α → OpenPartialHomeomorph W V3)
    (hcover : ∀ x, ∃ i, x ∈ (atlas i).source)
    (hrep : ∀ i, ∃ (B : Set E) (g : E → V3), FinitePiecewiseAffineOn g B ∧
      ∀ x ∈ (atlas i).source, (x : E) ∈ B ∧ atlas i x = g x)
    (G : W ≃ₜ W)
    (hG : ∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
      piecewiseAffineGroupoid V3)
    {V S : Set W} (hVD : V ⊆ (Subtype.val : W → E) ⁻¹' D)
    (hfix : EqOn G id Vᶜ)
    (himage : T = (Subtype.val : W → E) '' (G '' S)) :
    ∃ A' : Set W, A' ⊆ (Subtype.val : W → E) ⁻¹' D ∧
      Nonempty (ChartwisePLBall atlas A' S) := by
  obtain ⟨b'⟩ := exists_chartwisePLBall_in_carrier atlas hcover hrep
    hA (hAD.trans hDW)
  have hboundary : (Subtype.val : W → E) ⁻¹' T = G '' S := by
    rw [himage,preimage_image_eq _ Subtype.val_injective]
  rw [hboundary] at b'
  exact b'.exists_ball_before_supported_motion G (preimage_mono hAD) hVD hfix hcover hG

theorem exists_capped_ball_of_retained_ball
    {X E ι α : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {Q A T : Set X}
    (b : ChartwisePLBall e A T) (hAQ : A ⊆ Q) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F Q) {W D : Set E} (hQD : F '' Q ⊆ D) (hDW : D ⊆ W)
    (atlas : α → OpenPartialHomeomorph W V3)
    (hcover : ∀ x, ∃ i, x ∈ (atlas i).source)
    (hrep : ∀ i, ∃ (B : Set E) (g : E → V3), FinitePiecewiseAffineOn g B ∧
      ∀ x ∈ (atlas i).source, (x : E) ∈ B ∧ atlas i x = g x)
    (G : W ≃ₜ W)
    (hG : ∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
      piecewiseAffineGroupoid V3)
    {V S : Set W} (hVD : V ⊆ (Subtype.val : W → E) ⁻¹' D)
    (hfix : EqOn G id Vᶜ)
    (himage : F '' T = (Subtype.val : W → E) '' (G '' S)) :
    ∃ A' : Set W, A' ⊆ (Subtype.val : W → E) ⁻¹' D ∧
      Nonempty (ChartwisePLBall atlas A' S) := by
  exact exists_ball_of_moved_carrier_ball (b.finitePLBallPair_image hAQ F hF hFi)
    ((image_mono hAQ).trans hQD) hDW atlas hcover hrep G hG hVD hfix himage

end PoincareConjecture.M76
