import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleConnected
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open Set StdSimplexCore

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

theorem continuous_closedFaceSheet (c : A.ModTwoEdgeCocycle)
    {s : Finset ι} (hs : s ∈ A.faces) {i : ι} (hi : i ∈ s) (b : ZMod 2) :
    Continuous (fun q : {q : A.barycentricSpace | q.val ∈ barycentricFace s} =>
      (c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q.val, b)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨k, hk⟩ := A.exists_mem_openVertexStar q.val
  let U : Set {q : A.barycentricSpace | q.val ∈ barycentricFace s} :=
    {q | q.val ∈ A.openVertexStar k}
  have hU : IsOpen U := (A.isOpen_openVertexStar k).preimage continuous_subtype_val
  have hlocal : ContinuousOn
      (fun q : {q : A.barycentricSpace | q.val ∈ barycentricFace s} =>
        (c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q.val, b)) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := (c.sheet k (b + c.value i k)).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun z : U => z.property))
    apply hc.congr
    intro z
    have hks : k ∈ s := A.mem_face_of_mem_openVertexStar z.val.property z.property
    have hindex : c.bundle.indexAt z.val.val ∈ s :=
      A.mem_face_of_mem_openVertexStar z.val.property (c.bundle.mem_baseSet_at _)
    have he := c.compose s hs i hi k hks (c.bundle.indexAt z.val.val) hindex
    change (⟨z.val.val, (b + c.value i k) + c.value k (c.bundle.indexAt z.val.val)⟩ :
      c.bundle.TotalSpace) = ⟨z.val.val, b + c.value i (c.bundle.indexAt z.val.val)⟩
    rw [add_assoc, he]
  exact hlocal.continuousAt (hU.mem_nhds hk)

theorem closedFace_sheet_change (c : A.ModTwoEdgeCocycle)
    {s : Finset ι} (hs : s ∈ A.faces) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    {q : A.barycentricSpace} (hq : q.val ∈ barycentricFace s) (b : ZMod 2) :
    (c.bundle.localTriv j).toOpenPartialHomeomorph.symm (q, b + c.value i j) =
      (c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, b) := by
  have hk : c.bundle.indexAt q ∈ s :=
    A.mem_face_of_mem_openVertexStar hq (c.bundle.mem_baseSet_at q)
  have he := c.compose s hs i hi j hj (c.bundle.indexAt q) hk
  change (⟨q, (b + c.value i j) + c.value j (c.bundle.indexAt q)⟩ :
    c.bundle.TotalSpace) = ⟨q, b + c.value i (c.bundle.indexAt q)⟩
  rw [add_assoc, he]

noncomputable def closedFaceLift (c : A.ModTwoEdgeCocycle)
    {s : Finset ι} (hs : s ∈ A.faces) {i : ι} (hi : i ∈ s) (b : ZMod 2)
    {x y : A.barycentricSpace} (p : Path x y)
    (hp : ∀ t, (p t).val ∈ barycentricFace s) :
    Path ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (x, b))
      ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (y, b)) where
  toFun t := (c.bundle.localTriv i).toOpenPartialHomeomorph.symm (p t, b)
  continuous_toFun := (c.continuous_closedFaceSheet hs hi b).comp
    (p.continuous.subtype_mk hp)
  source' := by simp
  target' := by simp

theorem exists_closedFace_lift (c : A.ModTwoEdgeCocycle)
    {s : Finset ι} (hs : s ∈ A.faces) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (b : ZMod 2) {x y : A.barycentricSpace} (p : Path x y)
    (hp : ∀ t, (p t).val ∈ barycentricFace s) :
    ∃ L : Path ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (x, b))
      ((c.bundle.localTriv j).toOpenPartialHomeomorph.symm (y, b + c.value i j)),
      ∀ t, c.bundle.proj (L t) = p t := by
  have hy : y.val ∈ barycentricFace s := by simpa using hp 1
  exact ⟨(c.closedFaceLift hs hi b p hp).cast rfl
    (c.closedFace_sheet_change hs hi hj hy b), fun _ => rfl⟩

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
