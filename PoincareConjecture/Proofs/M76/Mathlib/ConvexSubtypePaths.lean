import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false

open Set
open scoped unitInterval

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def segmentIn (s : Set E) (a b : s)
    (hseg : segment ℝ (a : E) (b : E) ⊆ s) : Path a b where
  toFun t := ⟨Path.segment (a : E) (b : E) t,
    hseg (by rw [← Path.range_segment]; exact mem_range_self _)⟩
  continuous_toFun := (Path.segment (a : E) (b : E)).continuous.subtype_mk _
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

theorem segmentIn_apply (s : Set E) (a b : s)
    (hseg : segment ℝ (a : E) (b : E) ⊆ s) (t : unitInterval) :
    (segmentIn s a b hseg t : E) = AffineMap.lineMap (a : E) (b : E) (t : ℝ) := rfl

theorem homotopic_of_convex_range {U s : Set E} (hs : Convex ℝ s) (hsub : s ⊆ U)
    {a b : U} (p q : Path a b)
    (hp : ∀ t, (p t : E) ∈ s) (hq : ∀ t, (q t : E) ∈ s) : p.Homotopic q := by
  refine ⟨{
    toFun := fun z => ⟨AffineMap.lineMap (p z.2 : E) (q z.2 : E) (z.1 : ℝ),
      hsub (hs.lineMap_mem (hp z.2) (hq z.2) z.1.property)⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · apply Continuous.subtype_mk
    dsimp [AffineMap.lineMap_apply]
    fun_prop
  · intro t
    apply Subtype.ext
    simp
  · intro t
    apply Subtype.ext
    simp
  · intro t x hx
    rcases hx with rfl | rfl <;> apply Subtype.ext <;> simp

theorem segmentIn_mem_convex {U s : Set E} (hs : Convex ℝ s)
    (a b : U) (hseg : segment ℝ (a : E) (b : E) ⊆ U)
    (ha : (a : E) ∈ s) (hb : (b : E) ∈ s) (t : unitInterval) :
    (segmentIn U a b hseg t : E) ∈ s :=
  hs.lineMap_mem ha hb t.property

end Path

namespace Path.Homotopic

theorem concat_radial {X : Type*} [TopologicalSpace X] {n : ℕ}
    (a : Fin (n + 1) → X) (y : X)
    (r : (i : Fin (n + 1)) → Path y (a i))
    (p : (i : Fin n) → Path (a i.castSucc) (a i.succ))
    (hp : ∀ i, (p i).Homotopic ((r i.castSucc).symm.trans (r i.succ))) :
    (Path.concat a p).Homotopic ((r 0).symm.trans (r (Fin.last n))) := by
  induction n with
  | zero =>
    simpa only [Path.concat_zero, Fin.reduceLast] using (symm_trans (r 0)).symm
  | succ n ih =>
    rw [Path.concat_succ]
    have h := (ih (a ∘ Fin.castSucc) (fun i => r i.castSucc)
      (fun i => p i.castSucc) (fun i => hp i.castSucc)).hcomp (hp (Fin.last n))
    refine h.trans ?_
    apply Path.Homotopic.Quotient.eq.mp
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
    rw [Path.Homotopic.Quotient.trans_assoc,
      ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (r (Fin.last n).castSucc)),
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
    rfl

end Path.Homotopic
