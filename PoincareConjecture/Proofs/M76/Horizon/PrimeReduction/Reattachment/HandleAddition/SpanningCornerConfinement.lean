import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningReflectedCorner
import PoincareConjecture.Proofs.M76.Rigidity.CenteredHalfspaceCharts



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Half" => Set.prod (Set.prod I I) (Icc (0 : ℝ) 1)

theorem exists_confined_original_corner_sector
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {W S F Q O : Set X}
    {g : C3 → X} (hg : PolyhedralPLInCharts e g Half) (hgi : InjOn g Half)
    (hgW : MapsTo g Half W)
    (hgmarks : ∀ z ∈ Half,(g z ∈ S ↔ z.2 = 0) ∧
      (g z ∈ F ↔ z.1.1 = 0) ∧ (g z ∈ Q ↔ z.1.2 ≤ 0))
    (hO : IsOpen O) (hgO : g 0 ∈ O) :
    ∃ (δ : ℝ) (f : C3 → X), 0 < δ ∧ δ ≤ 1 ∧
      (∀ z,f z = g (δ • z)) ∧
      PolyhedralPLInCharts e f Half ∧ InjOn f Half ∧ f 0 = g 0 ∧
      MapsTo f Half (O ∩ W) ∧
      ∀ z ∈ Half,(f z ∈ S ↔ z.2 = 0) ∧
        (f z ∈ F ↔ z.1.1 = 0) ∧ (f z ∈ Q ↔ z.1.2 ≤ 0) := by
  let V : Set Half := (fun z => g z) ⁻¹' O
  have hV : IsOpen V := hO.preimage hg.continuousOn.domRestrict
  obtain ⟨U,hU,hUV⟩ := isOpen_induced_iff.mp hV
  have h0U : (0 : C3) ∈ U := by
    have h0 : (0 : C3) ∈ Half := by
      change ((0 : ℝ) ∈ I ∧ (0 : ℝ) ∈ I) ∧ (0 : ℝ) ∈ Icc 0 1
      norm_num
    change (⟨0,h0⟩ : Half) ∈ (Subtype.val : Half → C3) ⁻¹' U
    rw [hUV]
    exact hgO
  obtain ⟨ε,hε,hεU⟩ := CoordinateHalfBoxes.exists_box_subset hU h0U
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  let a : C3 →L[ℝ] C3 := δ • ContinuousLinearMap.id ℝ C3
  have haHalf (z : C3) (hz : z ∈ Half) : a z ∈ Half := by
    change ((-1 ≤ δ*z.1.1 ∧ δ*z.1.1 ≤ 1) ∧ (-1 ≤ δ*z.1.2 ∧ δ*z.1.2 ≤ 1)) ∧
      (0 ≤ δ*z.2 ∧ δ*z.2 ≤ 1)
    rcases hz with ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨he,hf⟩⟩
    constructor
    · constructor <;> constructor <;> nlinarith
    · constructor <;> nlinarith
  have haU (z : C3) (hz : z ∈ Half) : a z ∈ U := by
    apply hεU
    change ((-ε ≤ δ*z.1.1 ∧ δ*z.1.1 ≤ ε) ∧ (-ε ≤ δ*z.1.2 ∧ δ*z.1.2 ≤ ε)) ∧
      (-ε ≤ δ*z.2 ∧ δ*z.2 ≤ ε)
    rcases hz with ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨he,hf⟩⟩
    constructor
    · constructor <;> constructor <;> nlinarith
    · constructor <;> nlinarith
  let f := g ∘ a
  have hi := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKH,_⟩,_⟩,_⟩ :=
    (hi.prod hi).prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  change K.space = Half at hKH
  have hf : PolyhedralPLInCharts e f Half := by
    rw [←hKH]
    exact hg.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,K.affineOnFaces_affine a.toContinuousAffineMap⟩
      (fun z hz => haHalf z (hKH.subset hz))
  have hfi : InjOn f Half := by
    intro z hz w hw heq
    have h := hgi (haHalf z hz) (haHalf w hw) heq
    change δ • z = δ • w at h
    exact (smul_right_injective C3 hδ.ne') h
  refine ⟨δ,f,hδ,hδ1,fun _ => rfl,hf,hfi,?_,?_,?_⟩
  · change g (a 0) = g 0
    rw [map_zero]
  · intro z hz
    refine ⟨?_,hgW (haHalf z hz)⟩
    have hh : (⟨a z,haHalf z hz⟩ : Half) ∈ (Subtype.val : Half → C3) ⁻¹' U := haU z hz
    rw [hUV] at hh
    exact hh
  · intro z hz
    obtain ⟨hS,hF,hQ⟩ := hgmarks (a z) (haHalf z hz)
    change (g (a z) ∈ S ↔ z.2 = 0) ∧
      (g (a z) ∈ F ↔ z.1.1 = 0) ∧ (g (a z) ∈ Q ↔ z.1.2 ≤ 0)
    refine ⟨hS.trans ?_,hF.trans ?_,hQ.trans ?_⟩
    · change δ*z.2 = 0 ↔ z.2 = 0
      exact mul_eq_zero.trans (or_iff_right hδ.ne')
    · change δ*z.1.1 = 0 ↔ z.1.1 = 0
      exact mul_eq_zero.trans (or_iff_right hδ.ne')
    · change δ*z.1.2 ≤ 0 ↔ z.1.2 ≤ 0
      constructor <;> intro h <;> nlinarith

theorem exists_original_corner_chart_of_local_marked_sector
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S W Q F : Set X} {x : X}
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i,(e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃L[ℝ] C3) (hxB : x ∈ B.source) (hBx : B x = 0)
    (hQW : Q ⊆ W)
    (hW : ∀ z ∈ B.target,B.symm z ∈ W ↔ 0 ≤ (L z).2)
    (hS : ∀ z ∈ B.target,B.symm z ∈ S ↔ (L z).2 = 0)
    (hF : ∀ z ∈ B.target,B.symm z ∈ F ↔ (L z).1.1 = 0)
    (g : C3 → X) (hg : PolyhedralPLInCharts e g Half) (hgi : InjOn g Half)
    (hg0 : g 0 = x) (hgW : MapsTo g Half W)
    (hgmarks : ∀ z ∈ Half,(g z ∈ S ↔ z.2 = 0) ∧
      (g z ∈ F ↔ z.1.1 = 0) ∧ (g z ∈ Q ↔ z.1.2 ≤ 0)) :
    ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ (L (H y)).1.1 = 0) ∧
      (∀ y ∈ H.source,y ∈ Q ↔ (L (H y)).1.1 ≤ 0 ∧ (L (H y)).1.2 ≤ 0) ∧
      ∀ y ∈ H.source,y ∈ F ↔ (L (H y)).2 = 0 := by
  obtain ⟨_,f,_,_,_,hf,hfi,hf0,hfBW,hfmarks⟩ :=
    exists_confined_original_corner_sector hg hgi hgW hgmarks B.open_source (hg0.symm ▸ hxB)
  exact exists_original_corner_chart_of_marked_sector B hB L hxB hBx hQW hW hS hF
    f hf hfi (hf0.trans hg0) (fun _ hz => (hfBW hz).1)
    (fun _ hz => (hfBW hz).2) hfmarks

end PoincareConjecture.M76
