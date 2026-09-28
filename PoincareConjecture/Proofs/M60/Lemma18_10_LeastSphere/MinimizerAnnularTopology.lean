import PoincareConjecture.Proofs.M02.BallHomotopyExtension
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.StereographicConformal
import Mathlib.Topology.Piecewise

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

noncomputable section

namespace PoincareConjecture.M60

theorem suNullSphere_relative_caps
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (v : C(UnitTwoSphere, Y)) (hv : v.Nullhomotopic)
    (a b : C(X, UnitTwoSphere)) (S : Set X) (hab : EqOn a b S) :
    (v.comp a).HomotopicRel (v.comp b) S := by
  obtain ⟨F, hF⟩ := Proofs.M02.sphere_nullhomotopic_iff_extends_closedBall v |>.mp hv
  let a' : C(X, LoopAmbient) := ⟨fun x => (a x).val,
    continuous_subtype_val.comp a.continuous⟩
  let b' : C(X, LoopAmbient) := ⟨fun x => (b x).val,
    continuous_subtype_val.comp b.continuous⟩
  let H := ContinuousMap.Homotopy.affine a' b'
  have hH (z : unitInterval × X) : H z ∈ closedBall (0 : LoopAmbient) 1 :=
    (convex_closedBall (0 : LoopAmbient) 1).lineMap_mem
      (sphere_subset_closedBall (a z.2).property)
      (sphere_subset_closedBall (b z.2).property) z.1.property
  refine ⟨{
    toHomotopy := {
      toFun := fun z => F ⟨H z, hH z⟩
      continuous_toFun := F.continuous.comp (H.continuous.subtype_mk hH)
      map_zero_left := ?_
      map_one_left := ?_
    }
    prop' := ?_
  }⟩
  · intro x
    exact (congrArg F (Subtype.ext (H.apply_zero x))).trans (hF (a x))
  · intro x
    exact (congrArg F (Subtype.ext (H.apply_one x))).trans (hF (b x))
  · intro t x hx
    have hsame : H (t, x) = (a x).val := by
      change AffineMap.lineMap ((a x).val) ((b x).val) (t : ℝ) = _
      rw [← hab hx, AffineMap.lineMap_same_apply]
    exact (congrArg F (Subtype.ext hsame)).trans (hF (a x))

theorem suHomotopy_extend_closed
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {K : Set X} (hK : IsClosed K) (g : C(K, Y))
    (H : (f.restrict K).HomotopyRel g {x : K | x.val ∈ frontier K}) :
    ∃ h : C(X, Y), h.Homotopic f ∧
      (∀ x : K, h x = g x) ∧ ∀ x ∉ K, h x = f x := by
  classical
  let P : unitInterval × X → Y := fun z =>
    if hx : z.2 ∈ K then H (z.1, ⟨z.2, hx⟩) else f z.2
  let A : Set (unitInterval × X) := Prod.snd ⁻¹' K
  let B : Set (unitInterval × X) := Prod.snd ⁻¹' closure Kᶜ
  have hA : IsClosed A := hK.preimage continuous_snd
  have hB : IsClosed B := isClosed_closure.preimage continuous_snd
  have hcA : ContinuousOn P A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun z : A => H (z.val.1, ⟨z.val.2, z.property⟩)) :=
      H.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
    exact hc.congr (fun z => by
      dsimp only [Set.domRestrict, P]
      rw [dif_pos (show z.val.2 ∈ K from z.property)])
  have hcB : ContinuousOn P B := by
    apply (f.continuous.comp continuous_snd).continuousOn.congr
    intro z hz
    dsimp only [P]
    split_ifs with hx
    · exact H.eq_fst z.1 (show (⟨z.2, hx⟩ : K) ∈ {x : K | x.val ∈ frontier K} from by
        rw [frontier_eq_closure_inter_closure, hK.closure_eq]
        exact ⟨hx, hz⟩)
    · rfl
  have hcover : A ∪ B = univ := by
    ext z
    simp only [mem_union, mem_univ, iff_true]
    by_cases hz : z.2 ∈ K
    · exact Or.inl hz
    · exact Or.inr (subset_closure hz)
  have hc : Continuous P := by
    rw [← continuousOn_univ, ← hcover]
    exact hcA.union_of_isClosed hcB hA hB
  let h : C(X, Y) := ⟨fun x => P (1, x), hc.comp (continuous_const.prodMk continuous_id)⟩
  have H' : f.Homotopy h := {
    toFun := P
    continuous_toFun := hc
    map_zero_left := by
      intro x
      dsimp only [P]
      split_ifs with hx
      · exact H.apply_zero ⟨x, hx⟩
      · rfl
    map_one_left := fun _ => rfl
  }
  refine ⟨h, ⟨H'.symm⟩, ?_, ?_⟩
  · intro x
    change P (1, x.val) = g x
    dsimp only [P]
    rw [dif_pos x.property]
    exact H.apply_one x
  · intro x hx
    exact dif_neg hx

theorem suNullSphere_replace_closed_caps
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {K : Set X} (hK : IsClosed K)
    (v : C(UnitTwoSphere, Y)) (hv : v.Nullhomotopic)
    (a b : C(K, UnitTwoSphere)) (ha : ∀ x : K, v (a x) = f x)
    (hab : ∀ x : K, x.val ∈ frontier K → a x = b x) :
    ∃ h : C(X, Y), h.Homotopic f ∧
      (∀ x : K, h x = v (b x)) ∧ ∀ x ∉ K, h x = f x := by
  obtain ⟨H⟩ := suNullSphere_relative_caps v hv a b {x : K | x.val ∈ frontier K} hab
  have heq : v.comp a = f.restrict K := ContinuousMap.ext ha
  exact suHomotopy_extend_closed f hK (v.comp b) (H.cast heq rfl)

end PoincareConjecture.M60
