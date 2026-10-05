import Mathlib.Topology.Algebra.Group.Basic

/-!
# Straightening the graph of a continuous function

Subtracting a continuous function in the second coordinate is a
homeomorphism with the corresponding addition as inverse. The
absolute-value case straightens polygon corners. See Erickson,
Simple Polygons, pp. 2--3 and M76 derivation 98.
-/

set_option autoImplicit false

/-- The ambient shear subtracting a continuous graph from the
second coordinate. See M76 derivation 98. -/
def Homeomorph.subContinuousGraph {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    (f : X → G) (hf : Continuous f) : X × G ≃ₜ X × G where
  toFun q := (q.1, q.2 - f q.1)
  invFun q := (q.1, q.2 + f q.1)
  left_inv q := by simp
  right_inv q := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst))

/-- The shear takes exactly the prescribed graph to height zero.
See M76 derivation 98. -/
theorem Homeomorph.subContinuousGraph_snd_eq_zero_iff {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    (f : X → G) (hf : Continuous f) (q : X × G) :
    ((Homeomorph.subContinuousGraph f hf) q).2 = 0 ↔ q.2 = f q.1 := sub_eq_zero
