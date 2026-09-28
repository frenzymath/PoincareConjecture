import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitRegions
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionLinearImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePlanarShear










set_option autoImplicit false

open Set

namespace Polygon



theorem hasNonverticalEdges_of_injective_fst {n : ℕ} (P : Polygon (ℝ × ℝ) n)
    (hn : 2 ≤ n) (hinj : Function.Injective (fun i => (P i).1)) : P.HasNonverticalEdges := by
  let : NeZero n := ⟨by omega⟩
  intro i hi
  have hrot := (hinj hi).symm
  have h1 : (1 : Fin n) = 0 := add_left_cancel
    (show i + 1 = i + 0 by simpa only [finRotate_apply, add_zero] using hrot)
  have hval := congrArg Fin.val h1
  change 1 % n = 0 at hval
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  exact Nat.one_ne_zero hval





theorem region_partition_split {m n : ℕ} (u : Fin (m + 2) → ℝ × ℝ)
    (v : Fin (n + 2) → ℝ × ℝ)
    (hP : (mk (Fin.append u v)).HasSimplicialEdges)
    (hinj : Function.Injective (Fin.append u v))
    (hdiagonal : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside) :
    Disjoint (mk (Fin.snoc u (v 0))).inside (mk (Fin.snoc v (u 0))).inside ∧
      closure (mk (Fin.append u v)).inside =
        closure (mk (Fin.snoc u (v 0))).inside ∪ closure (mk (Fin.snoc v (u 0))).inside ∧
      closure (mk (Fin.snoc u (v 0))).inside ∩ closure (mk (Fin.snoc v (u 0))).inside =
        segment ℝ (u 0) (v 0) := by
  obtain ⟨e, he⟩ := (finite_range (Fin.append u v)).exists_planar_coordinates_injOn_fst
  let f := e.toLinearEquiv.toAffineEquiv.toAffineMap
  let u' := e ∘ u
  let v' := e ∘ v
  have hfun : Fin.append u' v' = e ∘ Fin.append u v := by
    funext i
    induction i using Fin.addCases <;> simp [u', v']
  have hmapP : mk (Fin.append u' v') = (mk (Fin.append u v)).affineImage f :=
    congrArg mk hfun
  have hmapQ : mk (Fin.snoc u' (v' 0)) = (mk (Fin.snoc u (v 0))).affineImage f := by
    change mk (Fin.snoc (e ∘ u) (e (v 0))) = mk (e ∘ Fin.snoc u (v 0))
    rw [Fin.comp_snoc]
  have hmapR : mk (Fin.snoc v' (u' 0)) = (mk (Fin.snoc v (u 0))).affineImage f := by
    change mk (Fin.snoc (e ∘ v) (e (u 0))) = mk (e ∘ Fin.snoc v (u 0))
    rw [Fin.comp_snoc]
  have hs : (mk (Fin.append u' v')).HasSimplicialEdges := by
    rw [hmapP]
    exact hasSimplicialEdges_affineImage _ hP f e.injective
  have hi : Function.Injective (Fin.append u' v') := by
    rw [hfun]
    exact e.injective.comp hinj
  have hfst : Function.Injective (fun i => ((Fin.append u' v') i).1) := by
    intro i j hij
    rw [hfun] at hij
    exact hinj (he (mem_range_self i) (mem_range_self j) hij)
  have hv := hasNonverticalEdges_of_injective_fst (mk (Fin.append u' v')) (by omega) hfst
  have hu : u 0 ∈ range (Fin.append u v) :=
    ⟨(0 : Fin (m + 2)).castAdd (n + 2), Fin.append_left u v 0⟩
  have hv0 : v 0 ∈ range (Fin.append u v) :=
    ⟨Fin.natAdd (m + 2) (0 : Fin (n + 2)), Fin.append_right u v 0⟩
  have hdv : (u' 0).1 ≠ (v' 0).1 := by
    intro h
    exact (Fin.append_injective_iff.mp hinj).2.2 0 0 (he hu hv0 h)
  have hd : openSegment ℝ (u' 0) (v' 0) ⊆ (mk (Fin.append u' v')).inside := by
    rw [hmapP, inside_linearImage]
    change openSegment ℝ (f (u 0)) (f (v 0)) ⊆ f '' (mk (Fin.append u v)).inside
    rw [← image_openSegment ℝ f]
    exact image_mono hdiagonal
  obtain ⟨hdis, hcover, hinter⟩ := region_partition_split_of_nonvertical u' v' hs hi hv hdv hd
  rw [hmapQ, hmapR, inside_linearImage, inside_linearImage] at hdis
  rw [hmapP, hmapQ, hmapR, closure_inside_linearImage,
    closure_inside_linearImage, closure_inside_linearImage] at hcover
  rw [hmapQ, hmapR, closure_inside_linearImage, closure_inside_linearImage] at hinter
  refine ⟨(disjoint_image_iff e.injective).mp hdis, ?_, ?_⟩
  · apply (image_injective.mpr e.injective)
    simpa only [image_union] using hcover
  · apply (image_injective.mpr e.injective)
    rw [image_inter e.injective]
    have hegd : e '' segment ℝ (u 0) (v 0) = segment ℝ (u' 0) (v' 0) :=
      image_segment ℝ f _ _
    rw [hegd]
    exact hinter

end Polygon
