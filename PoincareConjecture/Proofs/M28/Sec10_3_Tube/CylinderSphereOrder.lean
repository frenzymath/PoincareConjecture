import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereSides

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {X : Type u} [TopologicalSpace X]

private theorem signedHeight_opposite_order
    (φ₀ φ₁ : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1))
    (hdisj : ∀ x, cylinderSignedHeight φ₀ x = 0 → cylinderSignedHeight φ₁ x ≠ 0)
    (hlow : ∃ x, cylinderSignedHeight φ₀ x < 0 ∧ cylinderSignedHeight φ₁ x < 0)
    (hhigh : ∃ x, 0 < cylinderSignedHeight φ₀ x ∧ 0 < cylinderSignedHeight φ₁ x) :
    ((∀ x, cylinderSignedHeight φ₁ x = 0 → 0 < cylinderSignedHeight φ₀ x) ∧
      (∀ x, cylinderSignedHeight φ₀ x = 0 → cylinderSignedHeight φ₁ x < 0)) ∨
    ((∀ x, cylinderSignedHeight φ₁ x = 0 → cylinderSignedHeight φ₀ x < 0) ∧
      (∀ x, cylinderSignedHeight φ₀ x = 0 → 0 < cylinderSignedHeight φ₁ x)) := by
  have hne : ∀ x ∈ {x | cylinderSignedHeight φ₁ x = 0},
      cylinderSignedHeight φ₀ x ≠ 0 := by
    intro x hx hh
    exact hdisj x hh hx
  rcases (isPreconnected_cylinderSignedHeight_zero φ₁).mapsTo_Ioi_or_Iio
      (continuous_cylinderSignedHeight φ₀).continuousOn hne with hpos | hneg
  · refine Or.inl ⟨fun x hx => hpos hx, ?_⟩
    have havoid : ∀ x ∈ {x | cylinderSignedHeight φ₀ x < 0},
        cylinderSignedHeight φ₁ x ≠ 0 := by
      intro x hx hh
      change cylinderSignedHeight φ₀ x < 0 at hx
      have hpositive : 0 < cylinderSignedHeight φ₀ x := hpos hh
      exact (not_lt_of_ge hpositive.le) hx
    have hsubset : {x | cylinderSignedHeight φ₀ x < 0} ⊆
        {x | cylinderSignedHeight φ₁ x < 0} :=
      fun _ hx => (isPreconnected_cylinderSignedHeight_negative φ₀).gt_of_ne
        (continuous_cylinderSignedHeight φ₁).continuousOn havoid hlow hx
    have hclosure := closure_mono hsubset
    rw [closure_cylinderSignedHeight_negative, closure_cylinderSignedHeight_negative] at hclosure
    intro x hx
    exact lt_of_le_of_ne (hclosure (show cylinderSignedHeight φ₀ x ≤ 0 from hx.le))
      (hdisj x hx)
  · refine Or.inr ⟨fun x hx => hneg hx, ?_⟩
    have havoid : ∀ x ∈ {x | 0 < cylinderSignedHeight φ₀ x},
        cylinderSignedHeight φ₁ x ≠ 0 := by
      intro x hx hh
      change 0 < cylinderSignedHeight φ₀ x at hx
      have hnegative : cylinderSignedHeight φ₀ x < 0 := hneg hh
      exact (not_lt_of_ge hnegative.le) hx
    have hsubset : {x | 0 < cylinderSignedHeight φ₀ x} ⊆
        {x | 0 < cylinderSignedHeight φ₁ x} :=
      fun _ hx => (isPreconnected_cylinderSignedHeight_positive φ₀).lt_of_ne
        (continuous_cylinderSignedHeight φ₁).continuousOn havoid hhigh hx
    have hclosure := closure_mono hsubset
    rw [closure_cylinderSignedHeight_positive, closure_cylinderSignedHeight_positive] at hclosure
    intro x hx
    exact lt_of_le_of_ne (hclosure (show 0 ≤ cylinderSignedHeight φ₀ x from hx.ge))
      (Ne.symm (hdisj x hx))

theorem cylinderSignedHeight_opposite_order
    (phi0 phi1 : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1))
    (hdisj : ∀ x, cylinderSignedHeight phi0 x = 0 → cylinderSignedHeight phi1 x ≠ 0)
    (hlow : ∃ x, cylinderSignedHeight phi0 x < 0 ∧ cylinderSignedHeight phi1 x < 0)
    (hhigh : ∃ x, 0 < cylinderSignedHeight phi0 x ∧ 0 < cylinderSignedHeight phi1 x) :
    ((∀ x, cylinderSignedHeight phi1 x = 0 → 0 < cylinderSignedHeight phi0 x) ∧
      (∀ x, cylinderSignedHeight phi0 x = 0 → cylinderSignedHeight phi1 x < 0)) ∨
    ((∀ x, cylinderSignedHeight phi1 x = 0 → cylinderSignedHeight phi0 x < 0) ∧
      (∀ x, cylinderSignedHeight phi0 x = 0 → 0 < cylinderSignedHeight phi1 x)) :=
  signedHeight_opposite_order phi0 phi1 hdisj hlow hhigh

variable {M : Type u} [TopologicalSpace M] {U : TopologicalSpace.Opens M}

noncomputable def ambientCylinderSignedHeight
    (φ : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) (x : M) : ℝ := by
  classical
  exact if hx : x ∈ U then cylinderSignedHeight φ ⟨x, hx⟩ else 0

theorem ambientCylinderSignedHeight_apply
    (φ : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) {x : M} (hx : x ∈ U) :
    ambientCylinderSignedHeight φ x = cylinderSignedHeight φ ⟨x, hx⟩ := by
  simp only [ambientCylinderSignedHeight, dif_pos hx]

theorem continuousOn_ambientCylinderSignedHeight
    (φ : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) :
    ContinuousOn (ambientCylinderSignedHeight φ) (U : Set M) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : U => ambientCylinderSignedHeight φ (x : M))
  have heq : (fun x : U => ambientCylinderSignedHeight φ (x : M)) =
      cylinderSignedHeight φ := by
    funext x
    exact ambientCylinderSignedHeight_apply φ x.property
  rw [heq]
  exact continuous_cylinderSignedHeight φ

end PoincareConjecture.M28

namespace PoincareConjecture.OpenCylinderModel

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : TopologicalSpace.Opens M}

theorem exists_ordered_isotopic_sphere_heights
    (T : OpenCylinderModel (U : Set M)) {S₀ S₁ : Set M}
    (hS₀ : SmoothSphereIsotopicIn (U : Set M) S₀ T.middleSphere)
    (hS₁ : SmoothSphereIsotopicIn (U : Set M) S₁ T.middleSphere)
    (hdisj : Disjoint S₀ S₁) :
    ∃ (h₀ h₁ : M → ℝ) (a b : ℝ),
      0 < a ∧ a < 1 / 2 ∧ 1 / 2 < b ∧ b < 1 ∧
      ContinuousOn h₀ (U : Set M) ∧ ContinuousOn h₁ (U : Set M) ∧
      (∀ x ∈ U, h₀ x = 0 ↔ x ∈ S₀) ∧
      (∀ x ∈ U, h₁ x = 0 ↔ x ∈ S₁) ∧
      (∀ x ∈ U, (T.inverse x).2 < a → h₀ x < 0 ∧ h₁ x < 0) ∧
      (∀ x ∈ U, b < (T.inverse x).2 → 0 < h₀ x ∧ 0 < h₁ x) ∧
      (((∀ x ∈ U, x ∈ S₁ → 0 < h₀ x) ∧
        (∀ x ∈ U, x ∈ S₀ → h₁ x < 0)) ∨
       ((∀ x ∈ U, x ∈ S₁ → h₀ x < 0) ∧
        (∀ x ∈ U, x ∈ S₀ → 0 < h₁ x))) := by
  obtain ⟨φ₀, a₀, b₀, ha₀, ha₀half, hb₀half, hb₀, hs₀, ht₀⟩ :=
    T.exists_isotopic_sphere_coordinates hS₀
  obtain ⟨φ₁, a₁, b₁, ha₁, ha₁half, hb₁half, hb₁, hs₁, ht₁⟩ :=
    T.exists_isotopic_sphere_coordinates hS₁
  let h₀ : M → ℝ := ambientCylinderSignedHeight φ₀
  let h₁ : M → ℝ := ambientCylinderSignedHeight φ₁
  let a : ℝ := min a₀ a₁
  let b : ℝ := max b₀ b₁
  have ha : 0 < a := lt_min ha₀ ha₁
  have hahalf : a < 1 / 2 := (min_le_left _ _).trans_lt ha₀half
  have hbhalf : 1 / 2 < b := hb₀half.trans_le (le_max_left _ _)
  have hb : b < 1 := max_lt hb₀ hb₁
  have hz₀ (x : M) (hx : x ∈ U) : h₀ x = 0 ↔ x ∈ S₀ := by
    dsimp only [h₀]
    rw [ambientCylinderSignedHeight_apply φ₀ hx]
    exact sub_eq_zero.trans (hs₀ ⟨x, hx⟩)
  have hz₁ (x : M) (hx : x ∈ U) : h₁ x = 0 ↔ x ∈ S₁ := by
    dsimp only [h₁]
    rw [ambientCylinderSignedHeight_apply φ₁ hx]
    exact sub_eq_zero.trans (hs₁ ⟨x, hx⟩)
  have hlow (x : M) (hx : x ∈ U) (hh : (T.inverse x).2 < a) :
      h₀ x < 0 ∧ h₁ x < 0 := by
    dsimp only [h₀, h₁]
    rw [ambientCylinderSignedHeight_apply φ₀ hx, ambientCylinderSignedHeight_apply φ₁ hx]
    change ((φ₀ ⟨x, hx⟩).2 : ℝ) - 1 / 2 < 0 ∧
      ((φ₁ ⟨x, hx⟩).2 : ℝ) - 1 / 2 < 0
    rw [ht₀ ⟨x, hx⟩ (Or.inl (hh.trans_le (min_le_left _ _))),
      ht₁ ⟨x, hx⟩ (Or.inl (hh.trans_le (min_le_right _ _)))]
    exact ⟨sub_neg.mpr (hh.trans hahalf), sub_neg.mpr (hh.trans hahalf)⟩
  have hhigh (x : M) (hx : x ∈ U) (hh : b < (T.inverse x).2) :
      0 < h₀ x ∧ 0 < h₁ x := by
    dsimp only [h₀, h₁]
    rw [ambientCylinderSignedHeight_apply φ₀ hx, ambientCylinderSignedHeight_apply φ₁ hx]
    change 0 < ((φ₀ ⟨x, hx⟩).2 : ℝ) - 1 / 2 ∧
      0 < ((φ₁ ⟨x, hx⟩).2 : ℝ) - 1 / 2
    rw [ht₀ ⟨x, hx⟩ (Or.inr ((le_max_left _ _).trans_lt hh)),
      ht₁ ⟨x, hx⟩ (Or.inr ((le_max_right _ _).trans_lt hh))]
    exact ⟨sub_pos.mpr (hbhalf.trans hh), sub_pos.mpr (hbhalf.trans hh)⟩
  have hne (x : U) (hx₀ : cylinderSignedHeight φ₀ x = 0) :
      cylinderSignedHeight φ₁ x ≠ 0 := by
    intro hx₁
    exact Set.disjoint_left.mp hdisj
      ((hs₀ x).mp (sub_eq_zero.mp hx₀)) ((hs₁ x).mp (sub_eq_zero.mp hx₁))
  have hcommonlow : ∃ x : U,
      cylinderSignedHeight φ₀ x < 0 ∧ cylinderSignedHeight φ₁ x < 0 := by
    obtain ⟨x, hx⟩ := T.tail_nonempty false ha (hahalf.trans (by norm_num))
    have hx' := (T.mem_tail_iff_m28 false ha (hahalf.trans (by norm_num))).mp hx
    refine ⟨⟨x, hx'.1⟩, ?_⟩
    simpa only [h₀, h₁, ambientCylinderSignedHeight_apply _ hx'.1] using hlow x hx'.1 hx'.2
  have hcommonhigh : ∃ x : U,
      0 < cylinderSignedHeight φ₀ x ∧ 0 < cylinderSignedHeight φ₁ x := by
    have hbpos : 0 < b := (by norm_num : (0 : ℝ) < 1 / 2).trans hbhalf
    obtain ⟨x, hx⟩ := T.tail_nonempty true hbpos hb
    have hx' := (T.mem_tail_iff_m28 true hbpos hb).mp hx
    refine ⟨⟨x, hx'.1⟩, ?_⟩
    simpa only [h₀, h₁, ambientCylinderSignedHeight_apply _ hx'.1] using hhigh x hx'.1 hx'.2
  refine ⟨h₀, h₁, a, b, ha, hahalf, hbhalf, hb,
    continuousOn_ambientCylinderSignedHeight φ₀,
    continuousOn_ambientCylinderSignedHeight φ₁, hz₀, hz₁, hlow, hhigh, ?_⟩
  rcases signedHeight_opposite_order φ₀ φ₁ hne hcommonlow hcommonhigh with horder | horder
  · left
    constructor
    · intro x hx hs
      dsimp only [h₀]
      rw [ambientCylinderSignedHeight_apply φ₀ hx]
      exact horder.1 ⟨x, hx⟩ (sub_eq_zero.mpr ((hs₁ ⟨x, hx⟩).mpr hs))
    · intro x hx hs
      dsimp only [h₁]
      rw [ambientCylinderSignedHeight_apply φ₁ hx]
      exact horder.2 ⟨x, hx⟩ (sub_eq_zero.mpr ((hs₀ ⟨x, hx⟩).mpr hs))
  · right
    constructor
    · intro x hx hs
      dsimp only [h₀]
      rw [ambientCylinderSignedHeight_apply φ₀ hx]
      exact horder.1 ⟨x, hx⟩ (sub_eq_zero.mpr ((hs₁ ⟨x, hx⟩).mpr hs))
    · intro x hx hs
      dsimp only [h₁]
      rw [ambientCylinderSignedHeight_apply φ₁ hx]
      exact horder.2 ⟨x, hx⟩ (sub_eq_zero.mpr ((hs₀ ⟨x, hx⟩).mpr hs))

end PoincareConjecture.OpenCylinderModel
