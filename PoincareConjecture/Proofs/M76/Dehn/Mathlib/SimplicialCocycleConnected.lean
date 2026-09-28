import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleCover
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.FinCases











set_option autoImplicit false

open Set

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

private def falseCount (a b : Bool) : ℕ :=
  (if a = false then 1 else 0) + (if b = false then 1 else 0)

private theorem falseCount_zero {a b : Bool} :
    falseCount a b = 0 ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem falseCount_one {a b : Bool} :
    falseCount a b = 1 ↔ a ≠ b := by
  cases a <;> cases b <;> decide

private theorem falseCount_two {a b : Bool} :
    falseCount a b = 2 ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> decide

private theorem zmodTwo_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem falseCount_add (f : ZMod 2 → Bool) (a : ZMod 2) :
    falseCount (f (0 + a)) (f (1 + a)) = falseCount (f 0) (f 1) := by
  rcases zmodTwo_cases a with rfl | rfl
  · simp only [add_zero]
  · rw [zero_add, show (1 : ZMod 2) + 1 = 0 by decide]
    exact Nat.add_comm _ _

private theorem constant_of_count_zero (f : ZMod 2 → Bool)
    (h : falseCount (f 0) (f 1) = 0) (b : ZMod 2) : f b = true := by
  rcases zmodTwo_cases b with rfl | rfl
  · exact (falseCount_zero.mp h).1
  · exact (falseCount_zero.mp h).2

private theorem constant_of_count_two (f : ZMod 2 → Bool)
    (h : falseCount (f 0) (f 1) = 2) (b : ZMod 2) : f b = false := by
  rcases zmodTwo_cases b with rfl | rfl
  · exact (falseCount_two.mp h).1
  · exact (falseCount_two.mp h).2

private theorem existsUnique_false_of_count_one (f : ZMod 2 → Bool)
    (h : falseCount (f 0) (f 1) = 1) : ∃! b, f b = false := by
  have hne := falseCount_one.mp h
  cases h0 : f 0 with
  | false =>
    refine ⟨0, h0, ?_⟩
    intro b hb
    rcases zmodTwo_cases b with rfl | rfl
    · rfl
    · exact (hne (h0.trans hb.symm)).elim
  | true =>
    have h1 : f 1 = false := by
      cases hval : f 1 with
      | false => rfl
      | true => exact (hne (h0.trans hval.symm)).elim
    refine ⟨1, h1, ?_⟩
    intro b hb
    rcases zmodTwo_cases b with rfl | rfl
    · cases h0.symm.trans hb
    · rfl



noncomputable def sheet (c : A.ModTwoEdgeCocycle) (i : ι) (b : ZMod 2) :
    C(A.openVertexStar i, c.bundle.TotalSpace) where
  toFun q := (c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, b)
  continuous_toFun := continuous_subtype_val.comp
    ((c.bundle.localTriv i).sourceHomeomorphBaseSetProd.symm.continuous.comp
      (continuous_id.prodMk continuous_const))

private def fiberFalseCount (c : A.ModTwoEdgeCocycle)
    (h : c.bundle.TotalSpace → Bool) (q : A.barycentricSpace) : ℕ :=
  falseCount (h ⟨q, (0 : ZMod 2)⟩) (h ⟨q, (1 : ZMod 2)⟩)

private theorem fiberFalseCount_eq_local (c : A.ModTwoEdgeCocycle)
    (h : c.bundle.TotalSpace → Bool) (i : ι) (q : A.barycentricSpace) :
    fiberFalseCount c h q =
      falseCount (h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, 0)))
        (h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, 1))) := by
  exact (falseCount_add (fun b => h ⟨q, b⟩) (c.value i (c.bundle.indexAt q))).symm

private theorem continuous_fiberFalseCount (c : A.ModTwoEdgeCocycle)
    {h : c.bundle.TotalSpace → Bool} (hh : Continuous h) :
    Continuous (fiberFalseCount c h) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨i, hi⟩ := A.exists_mem_openVertexStar q
  have hlocal : ContinuousOn (fiberFalseCount c h) (A.openVertexStar i) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hcount : Continuous (fun z : Bool × Bool => falseCount z.1 z.2) :=
      continuous_of_discreteTopology
    exact (hcount.comp ((hh.comp (c.sheet i 0).continuous).prodMk
      (hh.comp (c.sheet i 1).continuous))).congr
      (fun x => (fiberFalseCount_eq_local c h i x).symm)
  exact hlocal.continuousAt ((A.isOpen_openVertexStar i).mem_nhds hi)

private theorem fiberFalseCount_eq_one (c : A.ModTwoEdgeCocycle)
    [ConnectedSpace A.barycentricSpace] {h : c.bundle.TotalSpace → Bool}
    (hh : Continuous h) {x y : c.bundle.TotalSpace} (hne : h x ≠ h y)
    (q : A.barycentricSpace) : fiberFalseCount c h q = 1 := by
  have hconstant (a b : A.barycentricSpace) :
      fiberFalseCount c h a = fiberFalseCount c h b :=
    PreconnectedSpace.constant inferInstance (continuous_fiberFalseCount c hh)
  have hvalues : fiberFalseCount c h q = 0 ∨ fiberFalseCount c h q = 1 ∨
      fiberFalseCount c h q = 2 := by
    unfold fiberFalseCount
    cases h ⟨q, (0 : ZMod 2)⟩ <;> cases h ⟨q, (1 : ZMod 2)⟩ <;> decide
  rcases hvalues with hzero | hone | htwo
  · have hx : h x = true := constant_of_count_zero (fun b => h ⟨x.1, b⟩)
      ((hconstant x.1 q).trans hzero) x.2
    have hy : h y = true := constant_of_count_zero (fun b => h ⟨y.1, b⟩)
      ((hconstant y.1 q).trans hzero) y.2
    exact (hne (hx.trans hy.symm)).elim
  · exact hone
  · have hx : h x = false := constant_of_count_two (fun b => h ⟨x.1, b⟩)
      ((hconstant x.1 q).trans htwo) x.2
    have hy : h y = false := constant_of_count_two (fun b => h ⟨y.1, b⟩)
      ((hconstant y.1 q).trans htwo) y.2
    exact (hne (hx.trans hy.symm)).elim






theorem isCoboundary_of_nonconstant_labeling (c : A.ModTwoEdgeCocycle)
    (hvertex : ∀ i : ι, {i} ∈ A.faces) [ConnectedSpace A.barycentricSpace]
    {h : c.bundle.TotalSpace → Bool} (hh : Continuous h)
    {x y : c.bundle.TotalSpace} (hne : h x ≠ h y) : c.IsCoboundary := by
  classical
  have hone (q : A.barycentricSpace) : fiberFalseCount c h q = 1 :=
    fiberFalseCount_eq_one c hh hne q
  have hlocalone (i : ι) (q : A.barycentricSpace) :
      falseCount (h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, 0)))
        (h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, 1))) = 1 :=
    (fiberFalseCount_eq_local c h i q).symm.trans (hone q)
  let vertex (i : ι) := A.barycentricVertex i (hvertex i)
  choose a ha using fun i => existsUnique_false_of_count_one
    (fun b => h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (vertex i, b)))
      (hlocalone i (vertex i))
  have hafalse (i : ι) {q : A.barycentricSpace} (hq : q ∈ A.openVertexStar i) :
      h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, a i)) = false := by
    have hcont : ContinuousOn
        (fun z => h ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (z, a i)))
        (A.openVertexStar i) :=
      continuousOn_iff_continuous_domRestrict.mpr (hh.comp (c.sheet i (a i)).continuous)
    have hconn := (A.isPathConnected_openVertexStar i (hvertex i)).isConnected.isPreconnected
    exact (hconn.constant hcont hq (A.barycentricVertex_mem_openVertexStar i (hvertex i))).trans
      (ha i).1
  refine ⟨a, ?_⟩
  intro s hs i hi j hj
  obtain ⟨q, hqi, hqj⟩ := A.openVertexStar_inter_nonempty_of_common_face hs hi hj
  have hchange : (c.bundle.localTriv j).toOpenPartialHomeomorph.symm (q, a i + c.value i j) =
      (c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, a i) := by
    rw [← c.trivialization_change hqi hqj (a i)]
    apply (c.bundle.localTriv j).toOpenPartialHomeomorph.left_inv
    exact hqj
  have hother : h ((c.bundle.localTriv j).toOpenPartialHomeomorph.symm
      (q, a i + c.value i j)) = false := by
    rw [hchange]
    exact hafalse i hqi
  obtain ⟨b, _, huniq⟩ := existsUnique_false_of_count_one
    (fun b => h ((c.bundle.localTriv j).toOpenPartialHomeomorph.symm (q, b))) (hlocalone j q)
  have heq : a i + c.value i j = a j :=
    (huniq _ hother).trans (huniq _ (hafalse j hqj)).symm
  have hdouble : a i + a i = 0 := by
    rcases zmodTwo_cases (a i) with hzero | hunit
    · rw [hzero]
      decide
    · rw [hunit]
      decide
  simpa only [← add_assoc, hdouble, zero_add] using congrArg (a i + ·) heq





theorem connectedSpace_of_not_isCoboundary (c : A.ModTwoEdgeCocycle)
    (hvertex : ∀ i : ι, {i} ∈ A.faces) [ConnectedSpace A.barycentricSpace]
    (hc : ¬c.IsCoboundary) : ConnectedSpace c.bundle.TotalSpace := by
  classical
  have hpre : PreconnectedSpace c.bundle.TotalSpace :=
    preconnectedSpace_of_forall_constant fun h hh x y => by
      by_contra hne
      exact hc (c.isCoboundary_of_nonconstant_labeling hvertex hh hne)
  exact
    { toPreconnectedSpace := hpre
      toNonempty := ⟨⟨Classical.arbitrary A.barycentricSpace, (0 : ZMod 2)⟩⟩ }

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
