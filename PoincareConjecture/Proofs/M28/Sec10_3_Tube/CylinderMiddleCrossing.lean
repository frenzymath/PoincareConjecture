import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderTripleCoordinates
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderComponentSide
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CoherentSphereOrder










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {X : Type*} [TopologicalSpace X]

private theorem cylinderSignedHeight_middle_signs_reverse
    (phiS phiC phiH : X ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1))
    (hCneg : ∀ x, cylinderSignedHeight phiC x = 0 → cylinderSignedHeight phiS x < 0)
    (hHneg : ∀ x, cylinderSignedHeight phiH x = 0 → cylinderSignedHeight phiS x < 0)
    (hCH : ∀ x, cylinderSignedHeight phiC x = 0 → cylinderSignedHeight phiH x ≠ 0)
    (hlow : ∃ x, cylinderSignedHeight phiS x < 0 ∧
      cylinderSignedHeight phiC x < 0 ∧ cylinderSignedHeight phiH x < 0)
    (hhigh : ∃ x, 0 < cylinderSignedHeight phiS x ∧
      0 < cylinderSignedHeight phiC x ∧ 0 < cylinderSignedHeight phiH x)
    {b q z p : X} (hb : cylinderSignedHeight phiS b = 0)
    (hq : cylinderSignedHeight phiC q = 0) (hz : cylinderSignedHeight phiH z = 0)
    {K P : Set X} (hK : IsPreconnected K) (hbK : b ∈ K) (hqK : q ∈ K)
    (havoidK : ∀ x ∈ K, cylinderSignedHeight phiH x ≠ 0)
    (hP : IsPreconnected P) (hzP : z ∈ P) (hpP : p ∈ P)
    (havoidP : ∀ x ∈ P, cylinderSignedHeight phiC x ≠ 0) :
    0 < cylinderSignedHeight phiC b ∧ cylinderSignedHeight phiC p < 0 := by
  obtain ⟨l, hlS, hlC, hlH⟩ := hlow
  obtain ⟨r, hrS, hrC, hrH⟩ := hhigh
  have hSC : ∀ x, cylinderSignedHeight phiS x = 0 →
      cylinderSignedHeight phiC x ≠ 0 := by
    intro x hxS hxC
    have h := hCneg x hxC
    rw [hxS] at h
    exact lt_irrefl _ h
  have hSH : ∀ x, cylinderSignedHeight phiS x = 0 →
      cylinderSignedHeight phiH x ≠ 0 := by
    intro x hxS hxH
    have h := hHneg x hxH
    rw [hxS] at h
    exact lt_irrefl _ h
  have hbC : 0 < cylinderSignedHeight phiC b := by
    rcases cylinderSignedHeight_opposite_order phiS phiC hSC
      ⟨l, hlS, hlC⟩ ⟨r, hrS, hrC⟩ with h | h
    · exact False.elim ((not_lt_of_ge (h.1 q hq).le) (hCneg q hq))
    · exact h.2 b hb
  have hbH : 0 < cylinderSignedHeight phiH b := by
    rcases cylinderSignedHeight_opposite_order phiS phiH hSH
      ⟨l, hlS, hlH⟩ ⟨r, hrS, hrH⟩ with h | h
    · exact False.elim ((not_lt_of_ge (h.1 z hz).le) (hHneg z hz))
    · exact h.2 b hb
  have hqH : 0 < cylinderSignedHeight phiH q :=
    hK.lt_of_ne (continuous_cylinderSignedHeight phiH).continuousOn
      havoidK ⟨b, hbK, hbH⟩ hqK
  have hHC : ∀ x, cylinderSignedHeight phiH x = 0 →
      cylinderSignedHeight phiC x < 0 := by
    rcases cylinderSignedHeight_opposite_order phiC phiH hCH
      ⟨l, hlC, hlH⟩ ⟨r, hrC, hrH⟩ with h | h
    · exact False.elim ((not_lt_of_ge hqH.le) (h.2 q hq))
    · exact h.1
  exact ⟨hbC, hP.gt_of_ne (continuous_cylinderSignedHeight phiC).continuousOn
    havoidP ⟨z, hzP, hHC z hz⟩ hpP⟩

end PoincareConjecture.M28

namespace PoincareConjecture.OpenCylinderModel

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : TopologicalSpace.Opens M}






theorem exists_middle_sphere_crossing_height
    (T : OpenCylinderModel (U : Set M)) {S C H F : Set M}
    (hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere)
    (hC : SmoothSphereIsotopicIn (U : Set M) C T.middleSphere)
    (hH : SmoothSphereIsotopicIn (U : Set M) H T.middleSphere)
    (hF : IsConnected F) (hFU : F ⊆ (U : Set M) \ S)
    (hcomponent : ∀ x ∈ F, connectedComponentIn ((U : Set M) \ S) x = F)
    (hSC : Disjoint S C) (hCH : Disjoint C H)
    (hHoutside : ∀ x ∈ H, x ∉ S ∧ x ∉ F)
    {b q z p : U} (hbS : (b : M) ∈ S) (hqC : (q : M) ∈ C)
    (hqF : (q : M) ∉ F) (hzHmem : (z : M) ∈ H)
    {K P : Set U} (hK : IsPreconnected K) (hbK : b ∈ K) (hqK : q ∈ K)
    (havoidK : ∀ x ∈ K, (x : M) ∉ H)
    (hP : IsPreconnected P) (hzP : z ∈ P) (hpP : p ∈ P)
    (havoidP : ∀ x ∈ P, (x : M) ∉ C) :
    ∃ h : U → ℝ, Continuous h ∧
      (∀ x : U, h x = 0 ↔ (x : M) ∈ C) ∧ h b < 0 ∧ 0 < h p := by
  obtain ⟨phiS, phiC, phiH, hzS, hzC, hzH, hlow, hhigh⟩ :=
    T.exists_three_isotopic_sphere_coordinates hS hC hH
  have hb0 := (hzS b).mpr hbS
  have hq0 := (hzC q).mpr hqC
  have hz0 := (hzH z).mpr hzHmem
  have hCavoid : ∀ x ∈ {x : U | cylinderSignedHeight phiC x = 0},
      cylinderSignedHeight phiS x ≠ 0 := by
    intro x hxC hxS
    exact Set.disjoint_left.mp hSC ((hzS x).mp hxS) ((hzC x).mp hxC)
  have hCHzero : ∀ x : U, cylinderSignedHeight phiC x = 0 →
      cylinderSignedHeight phiH x ≠ 0 := by
    intro x hxC hxH
    exact Set.disjoint_left.mp hCH ((hzC x).mp hxC) ((hzH x).mp hxH)
  have hKavoid : ∀ x ∈ K, cylinderSignedHeight phiH x ≠ 0 :=
    fun x hx hh => havoidK x hx ((hzH x).mp hh)
  have hPavoid : ∀ x ∈ P, cylinderSignedHeight phiC x ≠ 0 :=
    fun x hx hh => havoidP x hx ((hzC x).mp hh)
  rcases cylinderSignedHeight_component_half phiS hzS hF hFU hcomponent
    with hnegative | hpositive
  · have hqS : 0 < cylinderSignedHeight phiS q := by
      rcases lt_or_gt_of_ne (hCavoid q hq0) with h | h
      · exact False.elim (hqF ((hnegative q).mp h))
      · exact h
    have hCpos : ∀ x : U, cylinderSignedHeight phiC x = 0 →
        0 < cylinderSignedHeight phiS x := by
      intro x hx
      exact (isPreconnected_cylinderSignedHeight_zero phiC).lt_of_ne
        (continuous_cylinderSignedHeight phiS).continuousOn hCavoid ⟨q, hq0, hqS⟩ hx
    have hHpos : ∀ x : U, cylinderSignedHeight phiH x = 0 →
        0 < cylinderSignedHeight phiS x := by
      intro x hx
      have hout := hHoutside x ((hzH x).mp hx)
      have hne : cylinderSignedHeight phiS x ≠ 0 := fun hh => hout.1 ((hzS x).mp hh)
      rcases lt_or_gt_of_ne hne with h | h
      · exact False.elim (hout.2 ((hnegative x).mp h))
      · exact h
    obtain ⟨hb, hp⟩ := cylinderSignedHeight_middle_signs phiS phiC phiH
      hCpos hHpos hCHzero hlow hhigh hb0 hq0 hz0 hK hbK hqK hKavoid hP hzP hpP hPavoid
    exact ⟨cylinderSignedHeight phiC, continuous_cylinderSignedHeight phiC, hzC, hb, hp⟩
  · have hqS : cylinderSignedHeight phiS q < 0 := by
      rcases lt_or_gt_of_ne (hCavoid q hq0) with h | h
      · exact h
      · exact False.elim (hqF ((hpositive q).mp h))
    have hCneg : ∀ x : U, cylinderSignedHeight phiC x = 0 →
        cylinderSignedHeight phiS x < 0 := by
      intro x hx
      exact (isPreconnected_cylinderSignedHeight_zero phiC).gt_of_ne
        (continuous_cylinderSignedHeight phiS).continuousOn hCavoid ⟨q, hq0, hqS⟩ hx
    have hHneg : ∀ x : U, cylinderSignedHeight phiH x = 0 →
        cylinderSignedHeight phiS x < 0 := by
      intro x hx
      have hout := hHoutside x ((hzH x).mp hx)
      have hne : cylinderSignedHeight phiS x ≠ 0 := fun hh => hout.1 ((hzS x).mp hh)
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · exact False.elim (hout.2 ((hpositive x).mp h))
    obtain ⟨hb, hp⟩ := cylinderSignedHeight_middle_signs_reverse phiS phiC phiH
      hCneg hHneg hCHzero hlow hhigh hb0 hq0 hz0 hK hbK hqK hKavoid hP hzP hpP hPavoid
    refine ⟨fun x => -cylinderSignedHeight phiC x,
      (continuous_cylinderSignedHeight phiC).neg, ?_, neg_lt_zero.mpr hb, neg_pos.mpr hp⟩
    intro x
    exact neg_eq_zero.trans (hzC x)

end PoincareConjecture.OpenCylinderModel
