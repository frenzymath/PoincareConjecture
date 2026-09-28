import PoincareConjecture.Proofs.M54.ConnectedSum.Collars

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SmoothConnectedSumData

variable {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)

def selectedFirstRegion (U : Set A.carrier) : Set C.carrier :=
  S.first_region ∩ S.first_identify.inverse ⁻¹' U

def selectedSecondRegion (V : Set B.carrier) : Set C.carrier :=
  S.second_region ∩ S.second_identify.inverse ⁻¹' V

def selectedComponentRegion (U : Set A.carrier) (V : Set B.carrier) : Set C.carrier :=
  S.selectedFirstRegion U ∪ S.selectedSecondRegion V ∪
    S.collar '' (univ ×ˢ ({0} : Set ℝ))

theorem selectedFirstRegion_eq_image (U : Set A.carrier) :
    S.selectedFirstRegion U =
      S.first_identify.map '' (S.first_ball.closedBallᶜ ∩ U) := by
  ext x
  constructor
  · rintro ⟨hx, hU⟩
    refine ⟨S.first_identify.inverse x, ⟨?_, hU⟩, S.first_identify.right_inverse hx⟩
    exact S.first_identify.inverse_image.subset (mem_image_of_mem _ hx)
  · rintro ⟨a, ⟨ha, hU⟩, rfl⟩
    refine ⟨S.first_identify.map_image.subset (mem_image_of_mem _ ha), ?_⟩
    change S.first_identify.inverse (S.first_identify.map a) ∈ U
    rw [S.first_identify.left_inverse ha]
    exact hU

theorem selectedSecondRegion_eq_image (V : Set B.carrier) :
    S.selectedSecondRegion V =
      S.second_identify.map '' (S.second_ball.closedBallᶜ ∩ V) := by
  ext x
  constructor
  · rintro ⟨hx, hV⟩
    refine ⟨S.second_identify.inverse x, ⟨?_, hV⟩, S.second_identify.right_inverse hx⟩
    exact S.second_identify.inverse_image.subset (mem_image_of_mem _ hx)
  · rintro ⟨b, ⟨hb, hV⟩, rfl⟩
    refine ⟨S.second_identify.map_image.subset (mem_image_of_mem _ hb), ?_⟩
    change S.second_identify.inverse (S.second_identify.map b) ∈ V
    rw [S.second_identify.left_inverse hb]
    exact hV

theorem selectedFirstRegion_open {U : Set A.carrier} (hU : IsOpen U) :
    IsOpen (S.selectedFirstRegion U) :=
  S.first_identify.inverse_smooth.continuousOn.isOpen_inter_preimage S.first_open hU

theorem selectedSecondRegion_open {V : Set B.carrier} (hV : IsOpen V) :
    IsOpen (S.selectedSecondRegion V) :=
  S.second_identify.inverse_smooth.continuousOn.isOpen_inter_preimage S.second_open hV

theorem selectedComponentRegion_compl (U : Set A.carrier) (V : Set B.carrier) :
    (S.selectedComponentRegion U V)ᶜ =
      S.selectedFirstRegion Uᶜ ∪ S.selectedSecondRegion Vᶜ := by
  ext x
  constructor
  · intro hx
    have hxcover : x ∈ S.first_region ∪ S.second_region ∪
        S.collar '' (univ ×ˢ ({0} : Set ℝ)) := S.cover.symm ▸ mem_univ x
    rcases hxcover with (hfirst | hsecond) | hcentral
    · exact Or.inl ⟨hfirst, fun hU => hx (Or.inl (Or.inl ⟨hfirst, hU⟩))⟩
    · exact Or.inr ⟨hsecond, fun hV => hx (Or.inl (Or.inr ⟨hsecond, hV⟩))⟩
    · exact False.elim (hx (Or.inr hcentral))
  · rintro (hx | hx) ((hy | hy) | hy)
    · exact hx.2 hy.2
    · exact Set.disjoint_left.mp S.regions_disjoint hx.1 hy.1
    · exact Set.disjoint_left.mp S.central_disjoint hy (Or.inl hx.1)
    · exact Set.disjoint_left.mp S.regions_disjoint hy.1 hx.1
    · exact hx.2 hy.2
    · exact Set.disjoint_left.mp S.central_disjoint hy (Or.inr hx.1)

theorem selectedComponentRegion_closed {U : Set A.carrier} {V : Set B.carrier}
    (hU : IsClosed U) (hV : IsClosed V) :
    IsClosed (S.selectedComponentRegion U V) := by
  rw [← isOpen_compl_iff, S.selectedComponentRegion_compl]
  exact (S.selectedFirstRegion_open hU.isOpen_compl).union
    (S.selectedSecondRegion_open hV.isOpen_compl)

theorem negative_mem_selectedFirstRegion {U : Set A.carrier}
    (hU : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 0) :
    S.collar (z, s) ∈ S.selectedFirstRegion U := by
  refine ⟨S.negative_mem_first z hs, ?_⟩
  change S.first_identify.inverse (S.collar (z, s)) ∈ U
  rw [S.negative_gluing z s hs]
  have hr : 1 - s ∈ Ioo (1 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2]
  rw [S.first_identify.left_inverse (S.first_ball.radial_mem_complement z hr)]
  apply hU
  apply mem_image_of_mem
  simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (lt_trans zero_lt_one hr.1), mem_sphere_zero_iff_norm.mp z.property,
    mul_one] using hr.2

theorem positive_mem_selectedSecondRegion {V : Set B.carrier}
    (hV : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V)
    (z : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    S.collar (z, s) ∈ S.selectedSecondRegion V := by
  refine ⟨S.positive_mem_second z hs, ?_⟩
  change S.second_identify.inverse (S.collar (z, s)) ∈ V
  rw [S.positive_gluing z s hs]
  have hr : 1 + s ∈ Ioo (1 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2]
  rw [S.second_identify.left_inverse
    (S.second_ball.radial_mem_complement (S.sphere_gluing z) hr)]
  apply hV
  apply mem_image_of_mem
  simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (lt_trans zero_lt_one hr.1),
    mem_sphere_zero_iff_norm.mp (S.sphere_gluing z).property, mul_one] using hr.2

theorem collarBand_subset_selectedComponentRegion {U : Set A.carrier} {V : Set B.carrier}
    (hU : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U)
    (hV : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) :
    S.collarBand (-1) 1 ⊆ S.selectedComponentRegion U V := by
  rintro _ ⟨⟨z, s⟩, hs, rfl⟩
  rcases lt_trichotomy s 0 with h | h | h
  · exact Or.inl (Or.inl (S.negative_mem_selectedFirstRegion hU z ⟨hs.2.1, h⟩))
  · subst s
    exact Or.inr (mem_image_of_mem _ ⟨mem_univ z, mem_singleton 0⟩)
  · exact Or.inl (Or.inr (S.positive_mem_selectedSecondRegion hV z ⟨h, hs.2.2⟩))

theorem selectedComponentRegion_eq_union_collarBand {U : Set A.carrier} {V : Set B.carrier}
    (hU : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U)
    (hV : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) :
    S.selectedComponentRegion U V =
      S.selectedFirstRegion U ∪ S.selectedSecondRegion V ∪ S.collarBand (-1) 1 := by
  ext x
  constructor
  · rintro ((hx | hx) | ⟨⟨z, s⟩, hs, rfl⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · have hs0 : s = 0 := hs.2
      subst s
      exact Or.inr (mem_image_of_mem _ ⟨mem_univ z, by constructor <;> norm_num⟩)
  · rintro ((hx | hx) | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact S.collarBand_subset_selectedComponentRegion hU hV hx

theorem selectedComponentRegion_isClopen {U : Set A.carrier} {V : Set B.carrier}
    (hU : IsClopen U) (hV : IsClopen V)
    (hfirst : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U)
    (hsecond : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V) :
    IsClopen (S.selectedComponentRegion U V) := by
  refine ⟨S.selectedComponentRegion_closed hU.isClosed hV.isClosed, ?_⟩
  rw [S.selectedComponentRegion_eq_union_collarBand hfirst hsecond]
  exact ((S.selectedFirstRegion_open hU.isOpen).union
    (S.selectedSecondRegion_open hV.isOpen)).union S.collar_open

end PoincareConjecture.SmoothConnectedSumData
