import PoincareConjecture.Proofs.M25.AppA_21_Local.PuncturedProjectiveModel
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SmoothProjectiveDoubleModel

theorem exists_connected_sum_model
    {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    (D : PoincareConjecture.SmoothProjectiveDoubleModel Q) :
    ∃ T : PoincareConjecture.RealProjectiveThreeConnectedSumModel Q
        (inferInstance : TopologicalSpace Q),
      T.sphere = D.sphere ∧
      T.first_piece = D.first_region ∪ D.sphere ∧
      T.second_piece = D.second_region ∪ D.sphere ∧
      T.first_puncture = D.first_puncture ∧
      T.second_puncture = D.second_puncture := by
  let V : Set PoincareConjecture.RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 1
  have hV : IsOpen V := isOpen_univ.prod isOpen_Ioo
  let c : V → Q := fun z => D.collar z.1
  have hloc : IsLocalHomeomorph c := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    have hval := hV.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    exact D.collar_local_diffeomorph.isLocalHomeomorphOn.comp
      hval.isLocalHomeomorphOn (fun z _ => z.2)
  have hcinj : Function.Injective c := by
    intro x y h
    exact Subtype.ext (D.collar_injective x.2 y.2 h)
  have hce := (hloc.isOpenEmbedding_of_injective hcinj).isEmbedding
  let j : PoincareConjecture.UnitTwoSphere → V := fun q =>
    ⟨(q, 0), mem_prod.mpr ⟨mem_univ _, by constructor <;> norm_num⟩⟩
  let pr : V → PoincareConjecture.UnitTwoSphere := fun z => z.1.1
  have hj : Continuous j :=
    (continuous_id.prodMk continuous_const).subtype_mk _
  have hpr : Continuous pr := continuous_fst.comp continuous_subtype_val
  have hleft : Function.LeftInverse pr j := fun _ => rfl
  let sigma : PoincareConjecture.UnitTwoSphere → Q := fun q => D.collar (q, 0)
  have hsigma : Topology.IsEmbedding sigma :=
    hce.comp (hleft.isEmbedding hpr hj)
  have hrange : range sigma = D.sphere := by
    calc
      range sigma = D.collar '' (univ ×ˢ ({0} : Set ℝ)) := by
        ext x
        constructor
        · rintro ⟨q, hq⟩
          exact ⟨(q, 0), ⟨mem_univ _, mem_singleton 0⟩, hq⟩
        · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, hx⟩
          have hs0 : s = 0 := hs
          subst s
          exact ⟨q, hx⟩
      _ = D.sphere := D.collar_sphere
  let eS : D.sphere ≃ₜ PoincareConjecture.UnitTwoSphere :=
    (hsigma.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm
  have hunion :
      (D.first_region ∪ D.sphere) ∪ (D.second_region ∪ D.sphere) = univ := by
    calc
      (D.first_region ∪ D.sphere) ∪ (D.second_region ∪ D.sphere) =
          D.first_region ∪ D.second_region ∪ D.sphere := by
        ext x
        simp only [mem_union]
        tauto
      _ = univ := D.cover
  have hinter :
      (D.first_region ∪ D.sphere) ∩ (D.second_region ∪ D.sphere) = D.sphere := by
    ext x
    constructor
    · rintro ⟨hx1 | hxS, hx2 | hxS⟩
      · exact False.elim (disjoint_left.mp D.disjoint hx1 hx2)
      · exact hxS
      · exact hxS
      · exact hxS
    · intro hxS
      exact ⟨Or.inr hxS, Or.inr hxS⟩
  have hfirst : (D.first_region ∪ D.sphere) \ D.sphere = D.first_region := by
    ext x
    constructor
    · intro hx
      exact hx.1.resolve_right hx.2
    · intro hx
      exact ⟨Or.inl hx, fun hxS => disjoint_left.mp D.sphere_disjoint hxS (Or.inl hx)⟩
  have hsecond : (D.second_region ∪ D.sphere) \ D.sphere = D.second_region := by
    ext x
    constructor
    · intro hx
      exact hx.1.resolve_right hx.2
    · intro hx
      exact ⟨Or.inl hx, fun hxS => disjoint_left.mp D.sphere_disjoint hxS (Or.inr hx)⟩
  obtain ⟨e1, _, _⟩ :=
    PoincareConjecture.StandardPuncturedProjectiveCover.exists_punctured_homeomorph D.first_model
  obtain ⟨e2, _, _⟩ :=
    PoincareConjecture.StandardPuncturedProjectiveCover.exists_punctured_homeomorph D.second_model
  let T : PoincareConjecture.RealProjectiveThreeConnectedSumModel Q
      (inferInstance : TopologicalSpace Q) :=
    { sphere := D.sphere
      sphere_model := eS
      first_piece := D.first_region ∪ D.sphere
      second_piece := D.second_region ∪ D.sphere
      union_eq := hunion
      intersection_eq := hinter
      first_puncture := D.first_puncture
      second_puncture := D.second_puncture
      first_piece_model := (Homeomorph.setCongr hfirst).trans e1
      second_piece_model := (Homeomorph.setCongr hsecond).trans e2 }
  exact ⟨T, rfl, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.SmoothProjectiveDoubleModel
