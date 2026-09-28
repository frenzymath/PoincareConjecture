import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Subpath

noncomputable section

namespace Poincare.Topology

open Set unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X]

abbrev Loop (x : X) := Path x x

def PathIn (A : Set X) {x y : X} (p : Path x y) : Prop :=
  Set.range p ⊆ A

theorem pathIn_symm {A : Set X} {x y : X} {p : Path x y}
    (hp : PathIn A p) : PathIn A p.symm := by
  intro z hz
  apply hp
  rwa [Path.symm_range] at hz

theorem pathIn_trans_left {A : Set X} {x y z : X}
    {p : Path x y} {q : Path y z} (hp : PathIn A p) (hq : PathIn A q) :
    PathIn A (p.trans q) := by
  intro z hz
  rw [Path.trans_range] at hz
  exact hz.elim (fun hpz => hp hpz) (fun hqz => hq hqz)

theorem path_connector_insertion
    {x₀ x₁ x₂ : X}
    (p : Path x₀ x₁) (q : Path x₁ x₂) (g : Path x₀ x₁) :
    (p.trans q).Homotopic ((p.trans g.symm).trans (g.trans q)) := by
  have hinner : (g.symm.trans (g.trans q)).Homotopic q := by
    have h₁ : (g.symm.trans (g.trans q)).Homotopic ((g.symm.trans g).trans q) :=
      (Path.Homotopic.trans_assoc g.symm g q).symm
    have h₂ : ((g.symm.trans g).trans q).Homotopic
        ((Path.refl x₁).trans q) :=
      Path.Homotopic.hcomp (Path.Homotopic.symm_trans g)
        (Path.Homotopic.refl q)
    exact h₁.trans (h₂.trans (Path.Homotopic.refl_trans q))
  have hproduct : ((p.trans g.symm).trans (g.trans q)).Homotopic
      (p.trans q) := by
    have hassoc : ((p.trans g.symm).trans (g.trans q)).Homotopic
        (p.trans (g.symm.trans (g.trans q))) :=
      Path.Homotopic.trans_assoc p g.symm (g.trans q)
    exact hassoc.trans (Path.Homotopic.hcomp (Path.Homotopic.refl p) hinner)
  exact hproduct.symm

theorem loop_decomposition_two
    {x₀ x₁ : X} (A B : Set X)
    (p : Path x₀ x₁) (q : Path x₁ x₀) (g : Path x₀ x₁)
    (hp : PathIn A p) (hq : PathIn B q)
    (hg : PathIn (A ∩ B) g) :
    ∃ a b : Loop x₀,
      PathIn A a ∧ PathIn B b ∧
        (p.trans q).Homotopic (a.trans b) := by
  let a : Loop x₀ := p.trans g.symm
  let b : Loop x₀ := g.trans q
  have hga : PathIn A g := fun z hz => (hg hz).1
  have hgb : PathIn B g := fun z hz => (hg hz).2
  have ha : PathIn A a := by
    dsimp [a, PathIn]
    rw [Path.trans_range, Path.symm_range]
    exact Set.union_subset hp hga
  have hb : PathIn B b := by
    dsimp [b, PathIn]
    rw [Path.trans_range]
    exact Set.union_subset hgb hq
  have hproduct : (a.trans b).Homotopic (p.trans q) := by
    dsimp [a, b]
    exact (path_connector_insertion p q g).symm
  exact ⟨a, b, ha, hb, hproduct.symm⟩

abbrev CoveredLoop (x₀ : X) :=
  Σ A : Set X, {p : Loop x₀ // PathIn A p}

namespace CoveredLoop

def path {x₀ : X} (p : CoveredLoop x₀) : Loop x₀ :=
  p.2.1

theorem path_in {x₀ : X} (p : CoveredLoop x₀) : PathIn p.1 p.path :=
  p.2.2

end CoveredLoop

def coveredLoopProduct (x₀ : X) : List (CoveredLoop x₀) → Loop x₀
  | [] => Path.refl x₀
  | p :: ps => p.path.trans (coveredLoopProduct x₀ ps)

theorem coveredLoopProduct_append
    {x₀ : X} (ps qs : List (CoveredLoop x₀)) :
    (coveredLoopProduct x₀ (ps ++ qs)).Homotopic
      ((coveredLoopProduct x₀ ps).trans (coveredLoopProduct x₀ qs)) := by
  induction ps with
  | nil =>
      exact (Path.Homotopic.refl_trans (coveredLoopProduct x₀ qs)).symm
  | cons p ps ih =>
      have h₁ : (p.path.trans (coveredLoopProduct x₀ (ps ++ qs))).Homotopic
          (p.path.trans
            ((coveredLoopProduct x₀ ps).trans (coveredLoopProduct x₀ qs))) :=
        Path.Homotopic.hcomp (Path.Homotopic.refl p.path) ih
      have h₂ : ((p.path.trans (coveredLoopProduct x₀ ps)).trans
          (coveredLoopProduct x₀ qs)).Homotopic
          (p.path.trans
            ((coveredLoopProduct x₀ ps).trans (coveredLoopProduct x₀ qs))) :=
        Path.Homotopic.trans_assoc p.path (coveredLoopProduct x₀ ps)
          (coveredLoopProduct x₀ qs)
      exact h₁.trans h₂.symm

theorem coveredLoopProduct_append_single
    {x₀ : X} (ps : List (CoveredLoop x₀)) (p : CoveredLoop x₀) :
    (coveredLoopProduct x₀ (ps ++ [p])).Homotopic
      ((coveredLoopProduct x₀ ps).trans p.path) := by
  have htail : (coveredLoopProduct x₀ [p]).Homotopic p.path := by
    exact Path.Homotopic.trans_refl p.path
  exact (coveredLoopProduct_append ps [p]).trans
    (Path.Homotopic.hcomp (Path.Homotopic.refl (coveredLoopProduct x₀ ps)) htail)

inductive CoveredPathChain (x₀ : X) : Set X → X → Type u
  | single {A : Set X} {y : X}
      (p : Path x₀ y) (hp : PathIn A p) : CoveredPathChain x₀ A y
  | extend {A B : Set X} {y z : X}
      (c : CoveredPathChain x₀ A y)
      (p : Path y z) (hp : PathIn B p)
      (g : Path x₀ y) (hg : PathIn (A ∩ B) g) :
      CoveredPathChain x₀ B z

namespace CoveredPathChain

def toPath {x₀ : X} {A : Set X} {y : X}
    (c : CoveredPathChain x₀ A y) : Path x₀ y :=
  match c with
  | .single p _ => p
  | .extend c p _ _ _ => c.toPath.trans p

structure PrefixDecomposition
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) where
  loops : List (CoveredLoop x₀)
  boundary : Path x₀ y
  boundary_in : PathIn A boundary
  homotopic : c.toPath.Homotopic
    ((coveredLoopProduct x₀ loops).trans boundary)

def prefixDecomposition
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) :
    PrefixDecomposition c := by
  induction c with
  | single p hp =>
      exact
        { loops := []
          boundary := p
          boundary_in := hp
          homotopic := (Path.Homotopic.refl_trans p).symm }
  | @extend A B y z c p hp g hg ih =>
      have hgA : PathIn A g := fun w hw => (hg hw).1
      have hgB : PathIn B g := fun w hw => (hg hw).2
      have hnew : PathIn A (ih.boundary.trans g.symm) :=
        pathIn_trans_left ih.boundary_in (pathIn_symm hgA)
      let newLoop : CoveredLoop x₀ :=
        ⟨A, ⟨ih.boundary.trans g.symm, hnew⟩⟩
      have hboundary : PathIn B (g.trans p) :=
        pathIn_trans_left hgB hp
      refine
        { loops := ih.loops ++ [newLoop]
          boundary := g.trans p
          boundary_in := hboundary
          homotopic := ?_ }
      have h₀ : (c.toPath.trans p).Homotopic
          (((coveredLoopProduct x₀ ih.loops).trans ih.boundary).trans p) :=
        Path.Homotopic.hcomp ih.homotopic (Path.Homotopic.refl p)
      have h₁ : (((coveredLoopProduct x₀ ih.loops).trans ih.boundary).trans p).Homotopic
          ((coveredLoopProduct x₀ ih.loops).trans (ih.boundary.trans p)) :=
        Path.Homotopic.trans_assoc (coveredLoopProduct x₀ ih.loops) ih.boundary p
      have h₂ : ((coveredLoopProduct x₀ ih.loops).trans
          (ih.boundary.trans p)).Homotopic
          ((coveredLoopProduct x₀ ih.loops).trans
            ((ih.boundary.trans g.symm).trans (g.trans p))) :=
        Path.Homotopic.hcomp
          (Path.Homotopic.refl (coveredLoopProduct x₀ ih.loops))
          (path_connector_insertion ih.boundary p g)
      have h₃ : ((coveredLoopProduct x₀ ih.loops).trans
          ((ih.boundary.trans g.symm).trans (g.trans p))).Homotopic
          (((coveredLoopProduct x₀ ih.loops).trans
            (ih.boundary.trans g.symm)).trans (g.trans p)) :=
        (Path.Homotopic.trans_assoc (coveredLoopProduct x₀ ih.loops)
          (ih.boundary.trans g.symm) (g.trans p)).symm
      have happend : (coveredLoopProduct x₀ (ih.loops ++ [newLoop])).Homotopic
          ((coveredLoopProduct x₀ ih.loops).trans (ih.boundary.trans g.symm)) := by
        simpa [newLoop, CoveredLoop.path] using
          coveredLoopProduct_append_single ih.loops newLoop
      have h₄ : (((coveredLoopProduct x₀ ih.loops).trans
          (ih.boundary.trans g.symm)).trans (g.trans p)).Homotopic
          ((coveredLoopProduct x₀ (ih.loops ++ [newLoop])).trans (g.trans p)) :=
        Path.Homotopic.hcomp happend.symm (Path.Homotopic.refl (g.trans p))
      exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

theorem decompose_loop
    {x₀ : X} {A : Set X} (c : CoveredPathChain x₀ A x₀) :
    ∃ loops : List (CoveredLoop x₀),
      c.toPath.Homotopic (coveredLoopProduct x₀ loops) := by
  let d := c.prefixDecomposition
  let lastLoop : CoveredLoop x₀ := ⟨A, ⟨d.boundary, d.boundary_in⟩⟩
  refine ⟨d.loops ++ [lastLoop], ?_⟩
  have happend : (coveredLoopProduct x₀ (d.loops ++ [lastLoop])).Homotopic
      ((coveredLoopProduct x₀ d.loops).trans d.boundary) := by
    simpa [lastLoop, CoveredLoop.path] using
      coveredLoopProduct_append_single d.loops lastLoop
  exact d.homotopic.trans happend.symm

theorem decompose_loop_with_membership
    {x₀ : X} {A : Set X} (c : CoveredPathChain x₀ A x₀) :
    ∃ loops : List (CoveredLoop x₀),
      c.toPath.Homotopic (coveredLoopProduct x₀ loops) ∧
        ∀ p ∈ loops, PathIn p.1 p.path := by
  obtain ⟨loops, hloops⟩ := c.decompose_loop
  refine ⟨loops, hloops, ?_⟩
  intro p hp
  exact p.path_in

theorem loop_decomposition_of_covered_chain
    {x₀ : X} {A : Set X} (γ : Loop x₀)
    (c : CoveredPathChain x₀ A x₀) (hγ : γ.Homotopic c.toPath) :
    ∃ loops : List (CoveredLoop x₀),
      γ.Homotopic (coveredLoopProduct x₀ loops) := by
  obtain ⟨loops, hc⟩ := c.decompose_loop
  exact ⟨loops, hγ.trans hc⟩

theorem loop_decomposition_of_covered_chain_with_membership
    {x₀ : X} {A : Set X} (γ : Loop x₀)
    (c : CoveredPathChain x₀ A x₀) (hγ : γ.Homotopic c.toPath) :
    ∃ loops : List (CoveredLoop x₀),
      γ.Homotopic (coveredLoopProduct x₀ loops) ∧
        ∀ p ∈ loops, PathIn p.1 p.path := by
  obtain ⟨loops, hc, hmem⟩ := c.decompose_loop_with_membership
  exact ⟨loops, hγ.trans hc, hmem⟩

end CoveredPathChain

structure PathConnectedOpenCover (x₀ : X) (ι : Type v) where
  carrier : ι → Set X
  isOpen : ∀ i, IsOpen (carrier i)
  cover : (Set.univ : Set X) ⊆ ⋃ i, carrier i
  base_mem : ∀ i, x₀ ∈ carrier i
  pathConnected : ∀ i, IsPathConnected (carrier i)
  interPathConnected : ∀ i j, IsPathConnected (carrier i ∩ carrier j)

def CoveredPathChain.carrierSets {x₀ : X} {A : Set X} {y : X}
    (c : CoveredPathChain x₀ A y) : Set (Set X) :=
  match c with
  | .single _ _ => {A}
  | .extend c _ _ _ _ => insert A c.carrierSets

theorem CoveredPathChain.current_mem_carrierSets
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) :
    A ∈ c.carrierSets := by
  induction c with
  | single => simp [CoveredPathChain.carrierSets]
  | extend c _ _ _ _ ih =>
      simp [CoveredPathChain.carrierSets]

theorem CoveredPathChain.prefix_loops_mem_carrierSets
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) :
    ∀ p ∈ c.prefixDecomposition.loops, p.1 ∈ c.carrierSets := by
  induction c with
  | single => simp [prefixDecomposition]
  | @extend A B y z c p hp g hg ih =>
      intro q hq
      simp only [prefixDecomposition, List.mem_append, List.mem_singleton] at hq
      simp only [CoveredPathChain.carrierSets, Set.mem_insert_iff]
      rcases hq with hq | rfl
      · exact Or.inr (ih q hq)
      · exact Or.inr c.current_mem_carrierSets

theorem CoveredPathChain.decompose_loop_with_carrierSets
    {x₀ : X} {A : Set X} (c : CoveredPathChain x₀ A x₀) :
    ∃ loops : List (CoveredLoop x₀),
      c.toPath.Homotopic (coveredLoopProduct x₀ loops) ∧
      ∀ p ∈ loops, p.1 ∈ c.carrierSets := by
  let d := c.prefixDecomposition
  let lastLoop : CoveredLoop x₀ := ⟨A, ⟨d.boundary, d.boundary_in⟩⟩
  refine ⟨d.loops ++ [lastLoop], ?_, ?_⟩
  · have happend : (coveredLoopProduct x₀ (d.loops ++ [lastLoop])).Homotopic
        ((coveredLoopProduct x₀ d.loops).trans d.boundary) := by
      simpa [lastLoop, CoveredLoop.path] using
        coveredLoopProduct_append_single d.loops lastLoop
    exact d.homotopic.trans happend.symm
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact c.prefix_loops_mem_carrierSets p hp
    · exact c.current_mem_carrierSets

theorem CoveredPathChain.decompose_of_endpoint_eq_with_carrierSets
    {x₀ y : X} {A : Set X} (c : CoveredPathChain x₀ A y) (hy : y = x₀) :
    ∃ loops : List (CoveredLoop x₀),
      (c.toPath.cast rfl hy.symm).Homotopic (coveredLoopProduct x₀ loops) ∧
      ∀ p ∈ loops, p.1 ∈ c.carrierSets := by
  subst y
  simpa using c.decompose_loop_with_carrierSets

theorem pathIn_subpath_of_Icc_subset
    {x y : X} (γ : Path x y) (s t : I) (hst : s ≤ t)
    {A : Set X} (hA : Set.Icc s t ⊆ γ ⁻¹' A) :
    PathIn A (γ.subpath s t) := by
  intro z hz
  rw [Path.range_subpath_of_le γ s t hst] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact hA hr

structure CoveredSubdivisionPrefix
    {x₀ : X} {ι : Type v} (A : ι → Set X) (γ : Loop x₀)
    (t : ℕ → I) (index : ℕ → ι) (hstart : γ (t 0) = x₀) (n : ℕ) where
  chain : CoveredPathChain x₀ (A (index n)) (γ (t (n + 1)))
  homotopic : chain.toPath.Homotopic
    ((γ.subpath (t 0) (t (n + 1))).cast hstart.symm rfl)
  carrierSets_subset : chain.carrierSets ⊆ Set.range A

def coveredSubdivisionPrefix
    {x₀ : X} {ι : Type v} (A : ι → Set X)
    (hbase : ∀ i, x₀ ∈ A i)
    (hinter : ∀ i j, IsPathConnected (A i ∩ A j))
    (γ : Loop x₀) (t : ℕ → I) (index : ℕ → ι)
    (hstart : γ (t 0) = x₀) (hmono : Monotone t)
    (hsub : ∀ n, Set.Icc (t n) (t (n + 1)) ⊆ γ ⁻¹' A (index n))
    (n : ℕ) : CoveredSubdivisionPrefix A γ t index hstart n := by
  induction n with
  | zero =>
      have hp0 : PathIn (A (index 0)) (γ.subpath (t 0) (t 1)) :=
        pathIn_subpath_of_Icc_subset γ (t 0) (t 1)
          (hmono (Nat.zero_le 1)) (hsub 0)
      let p : Path x₀ (γ (t 1)) :=
        (γ.subpath (t 0) (t 1)).cast hstart.symm rfl
      have hp : PathIn (A (index 0)) p := by
        simpa [p, PathIn] using hp0
      refine ⟨.single p hp, Path.Homotopic.refl p, ?_⟩
      intro S hS
      simp only [CoveredPathChain.carrierSets, Set.mem_singleton_iff] at hS
      exact ⟨index 0, hS.symm⟩
  | succ n ih =>
      have hp : PathIn (A (index (n + 1)))
          (γ.subpath (t (n + 1)) (t (n + 2))) :=
        pathIn_subpath_of_Icc_subset γ _ _
          (hmono (Nat.le_succ (n + 1))) (hsub (n + 1))
      have hj_prev : γ (t (n + 1)) ∈ A (index n) :=
        hsub n ⟨hmono (Nat.le_succ n), le_rfl⟩
      have hj_next : γ (t (n + 1)) ∈ A (index (n + 1)) :=
        hsub (n + 1) ⟨le_rfl, hmono (Nat.le_succ (n + 1))⟩
      let joined := (hinter (index n) (index (n + 1))).joinedIn
        x₀ ⟨hbase (index n), hbase (index (n + 1))⟩
        (γ (t (n + 1))) ⟨hj_prev, hj_next⟩
      let g : Path x₀ (γ (t (n + 1))) := joined.somePath
      have hg : PathIn (A (index n) ∩ A (index (n + 1))) g := by
        intro z hz
        obtain ⟨s, rfl⟩ := hz
        exact joined.somePath_mem s
      let c := CoveredPathChain.extend ih.chain
        (γ.subpath (t (n + 1)) (t (n + 2))) hp g hg
      refine ⟨c, ?_, ?_⟩
      have h₁ : c.toPath.Homotopic
          (((γ.subpath (t 0) (t (n + 1))).cast hstart.symm rfl).trans
            (γ.subpath (t (n + 1)) (t (n + 2)))) := by
        exact Path.Homotopic.hcomp ih.homotopic
          (Path.Homotopic.refl (γ.subpath (t (n + 1)) (t (n + 2))))
      have hstep : ((γ.subpath (t 0) (t (n + 1))).trans
          (γ.subpath (t (n + 1)) (t (n + 2)))).Homotopic
          (γ.subpath (t 0) (t (n + 2))) :=
        ⟨Path.Homotopy.subpathTransSubpath γ (t 0) (t (n + 1)) (t (n + 2))⟩
      have h₂ := hstep.pathCast hstart.symm rfl
      · simpa [c] using h₁.trans h₂
      · intro S hS
        simp only [c, CoveredPathChain.carrierSets, Set.mem_insert_iff] at hS
        rcases hS with hS | hS
        · exact ⟨index (n + 1), hS.symm⟩
        · exact ih.carrierSets_subset hS

theorem loop_decomposition_of_pathConnectedOpenCover
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (γ : Loop x₀) :
    ∃ loops : List (CoveredLoop x₀),
      γ.Homotopic (coveredLoopProduct x₀ loops) ∧
      ∀ p ∈ loops, ∃ i, PathIn (cover.carrier i) p.path := by
  have hopen : ∀ i, IsOpen (γ ⁻¹' cover.carrier i) := fun i =>
    (cover.isOpen i).preimage γ.continuous
  have hcover : (Set.univ : Set I) ⊆ ⋃ i, γ ⁻¹' cover.carrier i := by
    intro s _
    rcases Set.mem_iUnion.1 (cover.cover (Set.mem_univ (γ s))) with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, htmono, ⟨m, htm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  choose index hindex using hsub
  have htend : t (m + 1) = 1 := htm (m + 1) (Nat.le_succ m)
  have hstart : γ (t 0) = x₀ := (congrArg γ ht0).trans γ.source
  let pref := coveredSubdivisionPrefix cover.carrier cover.base_mem
    cover.interPathConnected γ t index hstart htmono hindex m
  have hend : γ (t (m + 1)) = x₀ := (congrArg γ htend).trans γ.target
  have hwhole :
      (((γ.subpath (t 0) (t (m + 1))).cast hstart.symm rfl).cast
        rfl hend.symm) = γ := by
    ext s
    simp [Path.subpath, ht0, htend]
  have hγ : γ.Homotopic (pref.chain.toPath.cast rfl hend.symm) := by
    have hleft := (pref.homotopic.pathCast rfl hend.symm).symm
    simpa only [hwhole] using hleft
  obtain ⟨loops, hloops, hloop_carrier⟩ :=
    pref.chain.decompose_of_endpoint_eq_with_carrierSets hend
  refine ⟨loops, hγ.trans hloops, ?_⟩
  intro p hp
  rcases pref.carrierSets_subset (hloop_carrier p hp) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [hi]
  exact p.path_in

end Poincare.Topology
