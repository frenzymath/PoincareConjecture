import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

def Homeomorph.subContinuousGraph {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    (f : X → G) (hf : Continuous f) : X × G ≃ₜ X × G where
  toFun q := (q.1, q.2 - f q.1)
  invFun q := (q.1, q.2 + f q.1)
  left_inv q := by simp
  right_inv q := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst))

theorem Homeomorph.subContinuousGraph_snd_eq_zero_iff {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G]
    (f : X → G) (hf : Continuous f) (q : X × G) :
    ((Homeomorph.subContinuousGraph f hf) q).2 = 0 ↔ q.2 = f q.1 := sub_eq_zero
