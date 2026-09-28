import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.RelativeFrontierOpenness
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.ParameterPrismDomain








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem PLDomain.isOpen_original_proper_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {w : ℝ}
    (hR : PLDomain e R)
    (hw : 0 < w) (f : (V2 × ℝ) → X)
    (hf : PolyhedralPLInCharts e f (D2 ×ˢ Icc (-w) w))
    (hinj : InjOn f (D2 ×ˢ Icc (-w) w))
    (hinside : MapsTo f (D2 ×ˢ Icc (-w) w) R)
    (hproper : ∀ x ∈ D2 ×ˢ Icc (-w) w,
      f x ∈ frontier R ↔ x.1 ∈ Q2) :
    IsOpen ((Subtype.val : R → X) ⁻¹' (f '' (D2 ×ˢ Ioo (-w) w))) := by
  let C : Set (V2 × ℝ) := D2 ×ˢ Icc (-w) w
  let T : Set (V2 × ℝ) := D2 ×ˢ Ioo (-w) w
  let Z0 : Set (V2 × ℝ) := D2 ×ˢ ({-w, w} : Set ℝ)
  let B := f '' C
  let Z := f '' Z0
  have hwidth : -w < w := by linarith
  have hTC : T ⊆ C := fun _ hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hZC : Z0 ⊆ C := by
    rintro x ⟨hx, ht⟩
    change x.2 = -w ∨ x.2 = w at ht
    rcases ht with ht | ht
    · refine ⟨hx, ?_⟩
      rw [ht]
      exact left_mem_Icc.mpr hwidth.le
    · refine ⟨hx, ?_⟩
      rw [ht]
      exact right_mem_Icc.mpr hwidth.le
  have hpair : IsFinitePLBallPair (V2 × ℝ) C
      ((Q2 ×ˢ Icc (-w) w) ∪ Z0) :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod (isFinitePLBallPair_Icc hwidth)
  obtain ⟨ball⟩ := exists_chartwisePLBall_image hpair
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) :
      (V2 × ℝ) ≃L[ℝ] V3) hf subset_rfl hinj
  have hBfront : frontier B = f '' ((Q2 ×ˢ Icc (-w) w) ∪ Z0) := ball.frontier_eq
  have hBreg : closure (interior B) = B := ball.closure_interior
  have hZ : IsCompact Z :=
    ((isCompact_closedBall (0 : V2) 1).prod
      (isCompact_singleton.insert (-w))).image_of_continuousOn
      (hf.continuousOn.mono hZC)
  have hfront : frontier B ⊆ frontier R ∪ Z := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hBfront.subset hy
    rcases hx with hx | hx
    · exact Or.inl ((hproper x ⟨sphere_subset_closedBall hx.1, hx.2⟩).mpr hx.1)
    · exact Or.inr (mem_image_of_mem f hx)
  have hTimage : f '' T = B \ Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_image_of_mem f (hTC hx), ?_⟩
      rintro ⟨z, hz, hzx⟩
      have he : z = x := hinj (hZC hz) (hTC hx) hzx
      subst z
      have ht := hz.2
      change x.2 = -w ∨ x.2 = w at ht
      rcases ht with he | he
      · exact (ne_of_gt hx.2.1) he
      · exact (ne_of_lt hx.2.2) he
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      refine ⟨x, ⟨hx.1, ?_, ?_⟩, rfl⟩
      · by_contra h
        have he : x.2 = -w := le_antisymm (not_lt.mp h) hx.2.1
        exact hn (mem_image_of_mem f (show x ∈ Z0 from ⟨hx.1, Or.inl he⟩))
      · by_contra h
        have he : x.2 = w := le_antisymm hx.2.2 (not_lt.mp h)
        exact hn (mem_image_of_mem f (show x ∈ Z0 from ⟨hx.1, Or.inr he⟩))
  have hBR : B ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hinside hx
  have hopen := hR.isOpen_relative_sdiff_of_frontier_subset hBreg hBR hZ.isClosed hfront
  rwa [← hTimage] at hopen


end PoincareConjecture.M76
