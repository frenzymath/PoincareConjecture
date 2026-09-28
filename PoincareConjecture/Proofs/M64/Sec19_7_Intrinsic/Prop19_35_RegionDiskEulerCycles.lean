import PoincareConjecture.Proofs.Horizon.Topology.Surface.Combinatorial.Incidence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

namespace PoincareConjecture

open Matrix
open PoincareConjecture.Surface.Combinatorial.Incidence

noncomputable def m64BinarySingle {I : Type*} (i : I) : I → ZMod 2 := by
  classical
  exact fun j => if j = i then 1 else 0

@[simp]
theorem m64BinarySingle_apply_self {I : Type*} (i : I) :
    m64BinarySingle i i = 1 := by
  simp [m64BinarySingle]

@[simp]
theorem m64BinarySingle_apply_of_ne {I : Type*} {i j : I} (h : j ≠ i) :
    m64BinarySingle i j = 0 := by
  simp [m64BinarySingle, h]

def m64SelectedEdgeDeletionGraph {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ e, e ≠ e0 ∧ x e ≠ 0 ∧
    (((ends e).1 = a ∧ (ends e).2 = b) ∨
      ((ends e).1 = b ∧ (ends e).2 = a))
  symm := ⟨by
    rintro a b ⟨hab, e, he0, hxe, hends⟩
    exact ⟨hab.symm, e, he0, hxe, hends.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by
    intro a
    rintro ⟨haa, -⟩
    exact haa rfl⟩

theorem m64Intrinsic_selected_edge_endpoints_reachable_without
    {V E : Type*} [Finite V] [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hcycle : (incidenceMatrix ends).transpose.mulVecLin x = 0)
    (hx0 : x e0 ≠ 0)
    (hendpoints : (ends e0).1 ≠ (ends e0).2) :
    (m64SelectedEdgeDeletionGraph ends x e0).Reachable
      (ends e0).1 (ends e0).2 := by
  classical
  let _ := Fintype.ofFinite V
  let G := m64SelectedEdgeDeletionGraph ends x e0
  let u := (ends e0).1
  let v := (ends e0).2
  have huv : u ≠ v := by
    simpa [u, v] using hendpoints
  by_contra hreachable
  have hv : ¬ G.Reachable u v := by
    simpa [G, u, v] using hreachable
  let component : V → ZMod 2 := fun w => if G.Reachable u w then 1 else 0
  have hedges_same_component (e : E) (he0 : e ≠ e0) (hxe : x e ≠ 0) :
      G.Reachable u (ends e).1 ↔ G.Reachable u (ends e).2 := by
    by_cases hloop : (ends e).1 = (ends e).2
    · simp [hloop]
    · have hadj : G.Adj (ends e).1 (ends e).2 := by
        exact ⟨hloop, e, he0, hxe, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨fun h => h.trans hadj.reachable,
        fun h => h.trans hadj.symm.reachable⟩
  have hterm (e : E) (he0 : e ≠ e0) :
      x e * (component (ends e).1 + component (ends e).2) = 0 := by
    by_cases hxe : x e = 0
    · simp [hxe]
    · have hsame := hedges_same_component e he0 hxe
      by_cases hfirst : G.Reachable u (ends e).1
      · have hsecond : G.Reachable u (ends e).2 := hsame.mp hfirst
        simp [component, hfirst, hsecond, CharTwo.add_self_eq_zero]
      · have hsecond : ¬ G.Reachable u (ends e).2 := by
          exact fun h => hfirst (hsame.mpr h)
        simp [component, hfirst, hsecond]
  have hmulVec : (incidenceMatrix ends).transpose.mulVec x = 0 := by
    change (incidenceMatrix ends).transpose.mulVec x = 0 at hcycle
    exact hcycle
  have hdot : x ⬝ᵥ (incidenceMatrix ends).mulVec component = 0 := by
    rw [← Matrix.dotProduct_transpose_mulVec
      (incidenceMatrix ends) component x]
    rw [hmulVec]
    simp
  have hsum :
      (∑ e, x e * (component (ends e).1 + component (ends e).2)) = 0 := by
    simpa [dotProduct, incidenceMatrix_mulVec_apply] using hdot
  have hsum_single :
      (∑ e, x e * (component (ends e).1 + component (ends e).2)) = x e0 := by
    rw [Finset.sum_eq_single e0]
    · simp [component, u, v, hv]
    · intro e _ he0
      exact hterm e he0
    · simp
  exact hx0 (hsum_single.symm.trans hsum)

noncomputable def m64SelectedEdgeOfDart {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (d : (m64SelectedEdgeDeletionGraph ends x e0).Dart) : E :=
  Classical.choose d.adj.2

theorem m64SelectedEdgeOfDart_spec {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (d : (m64SelectedEdgeDeletionGraph ends x e0).Dart) :
    m64SelectedEdgeOfDart ends x e0 d ≠ e0 ∧
      x (m64SelectedEdgeOfDart ends x e0 d) ≠ 0 ∧
      ((((ends (m64SelectedEdgeOfDart ends x e0 d)).1 = d.fst ∧
          (ends (m64SelectedEdgeOfDart ends x e0 d)).2 = d.snd)) ∨
        ((ends (m64SelectedEdgeOfDart ends x e0 d)).1 = d.snd ∧
          (ends (m64SelectedEdgeOfDart ends x e0 d)).2 = d.fst)) := by
  exact Classical.choose_spec d.adj.2

theorem m64SelectedEdgeOfDart_ne {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (d : (m64SelectedEdgeDeletionGraph ends x e0).Dart) :
    m64SelectedEdgeOfDart ends x e0 d ≠ e0 :=
  (m64SelectedEdgeOfDart_spec ends x e0 d).1

theorem m64SelectedEdgeOfDart_nonzero {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (d : (m64SelectedEdgeDeletionGraph ends x e0).Dart) :
    x (m64SelectedEdgeOfDart ends x e0 d) ≠ 0 :=
  (m64SelectedEdgeOfDart_spec ends x e0 d).2.1

theorem m64SelectedEdgeOfDart_ends {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (d : (m64SelectedEdgeDeletionGraph ends x e0).Dart) :
    (((ends (m64SelectedEdgeOfDart ends x e0 d)).1 = d.fst ∧
        (ends (m64SelectedEdgeOfDart ends x e0 d)).2 = d.snd) ∨
      ((ends (m64SelectedEdgeOfDart ends x e0 d)).1 = d.snd ∧
        (ends (m64SelectedEdgeOfDart ends x e0 d)).2 = d.fst)) :=
  (m64SelectedEdgeOfDart_spec ends x e0 d).2.2

noncomputable def m64WalkEdgeChain {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    {a b : V}
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk a b) : E → ZMod 2 := by
  classical
  exact (p.darts.map fun d =>
    m64BinarySingle (m64SelectedEdgeOfDart ends x e0 d)).sum

@[simp]
theorem m64WalkEdgeChain_nil {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E) (a : V) :
    m64WalkEdgeChain ends x e0
      (SimpleGraph.Walk.nil :
        (m64SelectedEdgeDeletionGraph ends x e0).Walk a a) = 0 := by
  simp [m64WalkEdgeChain]

@[simp]
theorem m64WalkEdgeChain_cons {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    {a b c : V}
    (h : (m64SelectedEdgeDeletionGraph ends x e0).Adj a b)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk b c) :
    m64WalkEdgeChain ends x e0 (SimpleGraph.Walk.cons h p) =
      m64BinarySingle (m64SelectedEdgeOfDart ends x e0 ⟨(a, b), h⟩) +
        m64WalkEdgeChain ends x e0 p := by
  simp [m64WalkEdgeChain]

private theorem m64_incidence_transpose_mulVec_single
    {V E : Type*} [Fintype E]
    (ends : E → V × V) (e : E) :
    (incidenceMatrix ends).transpose.mulVec (m64BinarySingle e) =
      m64BinarySingle (ends e).1 + m64BinarySingle (ends e).2 := by
  classical
  have hsingle : m64BinarySingle e = Pi.single e 1 := by
    ext j
    simp [m64BinarySingle, Pi.single_apply, eq_comm]
  rw [hsingle]
  rw [Matrix.mulVec_single_one]
  ext w
  simp [incidenceMatrix, m64BinarySingle, eq_comm]

theorem m64SelectedEdgeOfDart_boundary
    {V E : Type*} [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (d : (m64SelectedEdgeDeletionGraph ends x e0).Dart) :
    (incidenceMatrix ends).transpose.mulVec
        (m64BinarySingle (m64SelectedEdgeOfDart ends x e0 d)) =
      m64BinarySingle d.fst + m64BinarySingle d.snd := by
  rw [m64_incidence_transpose_mulVec_single]
  rcases m64SelectedEdgeOfDart_ends ends x e0 d with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, add_comm]

theorem m64WalkEdgeChain_boundary
    {V E : Type*} [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    {a b : V}
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk a b) :
    (incidenceMatrix ends).transpose.mulVec
        (m64WalkEdgeChain ends x e0 p) =
      m64BinarySingle a + m64BinarySingle b := by
  classical
  induction p with
  | nil =>
      rw [m64WalkEdgeChain_nil, Matrix.mulVec_zero]
      ext w
      simp [CharTwo.add_self_eq_zero]
  | @cons a b c h p ih =>
      rw [m64WalkEdgeChain_cons, Matrix.mulVec_add,
        m64SelectedEdgeOfDart_boundary, ih]
      ext w
      simp only [Pi.add_apply]
      calc
        (m64BinarySingle a w + m64BinarySingle b w) +
            (m64BinarySingle b w + m64BinarySingle c w) =
            m64BinarySingle a w +
              (m64BinarySingle b w + m64BinarySingle b w) +
                m64BinarySingle c w := by ring
        _ = m64BinarySingle a w + m64BinarySingle c w := by
          rw [CharTwo.add_self_eq_zero]
          simp

theorem m64WalkEdgeChain_apply_eq_zero_of_x_eq_zero
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    {a b : V}
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk a b)
    {e : E} (he : x e = 0) :
    m64WalkEdgeChain ends x e0 p e = 0 := by
  classical
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
      rw [m64WalkEdgeChain_cons]
      simp only [Pi.add_apply]
      have hchosen : m64SelectedEdgeOfDart ends x e0 ⟨(a, b), h⟩ ≠ e := by
        intro hce
        have hn := m64SelectedEdgeOfDart_nonzero ends x e0 ⟨(a, b), h⟩
        rw [hce, he] at hn
        exact hn rfl
      rw [m64BinarySingle_apply_of_ne hchosen.symm, ih]
      simp

theorem m64WalkEdgeChain_apply_e0
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    {a b : V}
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk a b) :
    m64WalkEdgeChain ends x e0 p e0 = 0 := by
  classical
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
      rw [m64WalkEdgeChain_cons]
      have hchosen := m64SelectedEdgeOfDart_ne ends x e0 ⟨(a, b), h⟩
      rw [Pi.add_apply, m64BinarySingle_apply_of_ne (Ne.symm hchosen), ih]
      simp

theorem m64WalkEdgeChain_support_subset_chosen
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    {a b : V}
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk a b) :
    Function.support (m64WalkEdgeChain ends x e0 p) ⊆
      {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e} := by
  classical
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
      intro e he
      by_cases hhead : m64SelectedEdgeOfDart ends x e0 ⟨(a, b), h⟩ = e
      · exact ⟨⟨(a, b), h⟩, by simp, hhead⟩
      · have htail : m64WalkEdgeChain ends x e0 p e ≠ 0 := by
          intro htail
          apply he
          rw [m64WalkEdgeChain_cons, Pi.add_apply,
            m64BinarySingle_apply_of_ne (Ne.symm hhead), htail]
          simp
        obtain ⟨d, hd, hde⟩ := ih htail
        exact ⟨d, by simp [hd], hde⟩

noncomputable def m64SelectedWalkCycleVector {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2) : E → ZMod 2 := by
  classical
  exact m64WalkEdgeChain ends x e0 p + m64BinarySingle e0

theorem m64SelectedWalkCycleVector_kernel
    {V E : Type*} [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2) :
    (incidenceMatrix ends).transpose.mulVecLin
      (m64SelectedWalkCycleVector ends x e0 p) = 0 := by
  classical
  change (incidenceMatrix ends).transpose.mulVec
    (m64SelectedWalkCycleVector ends x e0 p) = 0
  rw [m64SelectedWalkCycleVector, Matrix.mulVec_add,
    m64WalkEdgeChain_boundary, m64_incidence_transpose_mulVec_single]
  ext w
  simp only [Pi.add_apply, Pi.zero_apply]
  calc
    (m64BinarySingle (ends e0).1 w + m64BinarySingle (ends e0).2 w) +
        (m64BinarySingle (ends e0).1 w + m64BinarySingle (ends e0).2 w) =
        (m64BinarySingle (ends e0).1 w + m64BinarySingle (ends e0).1 w) +
          (m64BinarySingle (ends e0).2 w + m64BinarySingle (ends e0).2 w) := by
            ring
    _ = 0 := by simp [CharTwo.add_self_eq_zero]

theorem m64SelectedWalkCycleVector_ne_zero
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2) :
    m64SelectedWalkCycleVector ends x e0 p ≠ 0 := by
  classical
  intro hzero
  have he0 := congrFun hzero e0
  simp only [m64SelectedWalkCycleVector, Pi.add_apply, Pi.zero_apply] at he0
  rw [m64WalkEdgeChain_apply_e0] at he0
  simp at he0

theorem m64SelectedWalkCycleVector_support_subset
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hx0 : x e0 ≠ 0)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2) :
    Function.support (m64SelectedWalkCycleVector ends x e0 p) ⊆
      Function.support x := by
  classical
  intro e hecycle
  by_contra hxe
  have hxe_zero : x e = 0 := not_ne_iff.mp hxe
  have he0 : e ≠ e0 := by
    intro heq
    subst e
    exact hx0 hxe_zero
  apply hecycle
  simp [m64SelectedWalkCycleVector,
    m64WalkEdgeChain_apply_eq_zero_of_x_eq_zero ends x e0 p hxe_zero,
    he0]

theorem m64SelectedWalkCycleVector_support_subset_chosen
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2) :
    Function.support (m64SelectedWalkCycleVector ends x e0 p) ⊆
      ({e0} ∪
        {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}) := by
  classical
  intro e hecycle
  by_cases he0 : e = e0
  · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr he0)
  · apply Set.mem_union_right
    apply m64WalkEdgeChain_support_subset_chosen ends x e0 p
    intro hchain
    apply hecycle
    simp [m64SelectedWalkCycleVector, hchain, he0]

theorem m64SelectedWalkChosenEdges_subset_support
    {V E : Type*}
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hx0 : x e0 ≠ 0)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2) :
    ({e0} ∪
        {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}) ⊆
      Function.support x := by
  intro e he
  rcases he with he | ⟨d, -, hde⟩
  · have heq : e = e0 := Set.mem_singleton_iff.mp he
    change x e ≠ 0
    simpa only [heq] using hx0
  · rw [← hde]
    exact m64SelectedEdgeOfDart_nonzero ends x e0 d

theorem m64SelectedWalkCycleVector_support_eq_of_minimal
    {V E : Type*} [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hx0 : x e0 ≠ 0)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2)
    (hminimal : ∀ y : E → ZMod 2,
      (incidenceMatrix ends).transpose.mulVecLin y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y) :
    Function.support (m64SelectedWalkCycleVector ends x e0 p) =
      Function.support x := by
  apply Set.Subset.antisymm
  · exact m64SelectedWalkCycleVector_support_subset ends x e0 hx0 p
  · exact hminimal _ (m64SelectedWalkCycleVector_kernel ends x e0 p)
      (m64SelectedWalkCycleVector_ne_zero ends x e0 p)
      (m64SelectedWalkCycleVector_support_subset ends x e0 hx0 p)

theorem m64SelectedWalkCycleVector_exact_support_of_minimal
    {V E : Type*} [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hx0 : x e0 ≠ 0)
    (p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
      (ends e0).1 (ends e0).2)
    (hminimal : ∀ y : E → ZMod 2,
      (incidenceMatrix ends).transpose.mulVecLin y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y) :
    Function.support (m64SelectedWalkCycleVector ends x e0 p) =
        ({e0} ∪
          {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}) ∧
      ({e0} ∪
          {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}) =
        Function.support x := by
  let chosenEdges : Set E := {e0} ∪
    {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}
  have hcycle_eq := m64SelectedWalkCycleVector_support_eq_of_minimal
    ends x e0 hx0 p hminimal
  have hcycle_chosen :
      Function.support (m64SelectedWalkCycleVector ends x e0 p) ⊆ chosenEdges := by
    simpa only [chosenEdges] using
      m64SelectedWalkCycleVector_support_subset_chosen ends x e0 p
  have hchosen_x : chosenEdges ⊆ Function.support x := by
    simpa only [chosenEdges] using
      m64SelectedWalkChosenEdges_subset_support ends x e0 hx0 p
  have hx_chosen : Function.support x ⊆ chosenEdges := by
    rw [← hcycle_eq]
    exact hcycle_chosen
  have hchosen_eq : chosenEdges = Function.support x :=
    Set.Subset.antisymm hchosen_x hx_chosen
  exact ⟨hcycle_eq.trans hchosen_eq.symm, hchosen_eq⟩

theorem m64Intrinsic_exists_path_with_cycle_support
    {V E : Type*} [Finite V] [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hcycle : (incidenceMatrix ends).transpose.mulVecLin x = 0)
    (hx0 : x e0 ≠ 0)
    (hendpoints : (ends e0).1 ≠ (ends e0).2)
    (hminimal : ∀ y : E → ZMod 2,
      (incidenceMatrix ends).transpose.mulVecLin y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y) :
    ∃ p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
        (ends e0).1 (ends e0).2,
      p.IsPath ∧ ¬ p.Nil ∧
        Function.support (m64SelectedWalkCycleVector ends x e0 p) =
          Function.support x := by
  have hreachable := m64Intrinsic_selected_edge_endpoints_reachable_without
    ends x e0 hcycle hx0 hendpoints
  obtain ⟨p, hp⟩ := hreachable.exists_isPath
  exact ⟨p, hp, SimpleGraph.Walk.not_nil_of_ne hendpoints,
    m64SelectedWalkCycleVector_support_eq_of_minimal ends x e0 hx0 p hminimal⟩

theorem m64Intrinsic_exists_path_with_exact_cycle_support
    {V E : Type*} [Finite V] [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hcycle : (incidenceMatrix ends).transpose.mulVecLin x = 0)
    (hx0 : x e0 ≠ 0)
    (hendpoints : (ends e0).1 ≠ (ends e0).2)
    (hminimal : ∀ y : E → ZMod 2,
      (incidenceMatrix ends).transpose.mulVecLin y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y) :
    ∃ p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
        (ends e0).1 (ends e0).2,
      p.IsPath ∧ ¬ p.Nil ∧
        Function.support (m64SelectedWalkCycleVector ends x e0 p) =
          ({e0} ∪
            {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}) ∧
        ({e0} ∪
            {e | ∃ d ∈ p.darts, m64SelectedEdgeOfDart ends x e0 d = e}) =
          Function.support x := by
  have hreachable := m64Intrinsic_selected_edge_endpoints_reachable_without
    ends x e0 hcycle hx0 hendpoints
  obtain ⟨p, hp⟩ := hreachable.exists_isPath
  obtain ⟨hcycle_chosen, hchosen_x⟩ :=
    m64SelectedWalkCycleVector_exact_support_of_minimal
      ends x e0 hx0 p hminimal
  exact ⟨p, hp, SimpleGraph.Walk.not_nil_of_ne hendpoints,
    hcycle_chosen, hchosen_x⟩

theorem m64Intrinsic_minimal_cycle_eq_edge_union_path
    {V E : Type*} [Finite V] [Fintype E]
    (ends : E → V × V) (x : E → ZMod 2) (e0 : E)
    (hcycle : (incidenceMatrix ends).transpose.mulVecLin x = 0)
    (hx0 : x e0 ≠ 0)
    (hendpoints : (ends e0).1 ≠ (ends e0).2)
    (hminimal : ∀ y : E → ZMod 2,
      (incidenceMatrix ends).transpose.mulVecLin y = 0 → y ≠ 0 →
      Function.support y ⊆ Function.support x →
      Function.support x ⊆ Function.support y) :
    ∃ p : (m64SelectedEdgeDeletionGraph ends x e0).Walk
        (ends e0).1 (ends e0).2,
      p.IsPath ∧
        ∃ chosen : (m64SelectedEdgeDeletionGraph ends x e0).Dart → E,
          (∀ d, chosen d ≠ e0 ∧ x (chosen d) ≠ 0 ∧
            (((ends (chosen d)).1 = d.fst ∧ (ends (chosen d)).2 = d.snd) ∨
              ((ends (chosen d)).1 = d.snd ∧ (ends (chosen d)).2 = d.fst))) ∧
          ∀ e, x e ≠ 0 ↔
            e = e0 ∨ ∃ d ∈ p.darts, chosen d = e := by
  obtain ⟨p, hp, -, -, hchosen_x⟩ :=
    m64Intrinsic_exists_path_with_exact_cycle_support
      ends x e0 hcycle hx0 hendpoints hminimal
  refine ⟨p, hp, m64SelectedEdgeOfDart ends x e0, ?_, ?_⟩
  · intro d
    exact m64SelectedEdgeOfDart_spec ends x e0 d
  · intro e
    change e ∈ Function.support x ↔ _
    rw [← hchosen_x]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]

end PoincareConjecture
