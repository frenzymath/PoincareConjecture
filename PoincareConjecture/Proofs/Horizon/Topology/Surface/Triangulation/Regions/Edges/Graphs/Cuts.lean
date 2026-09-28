


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.CutChains







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable {D : FiniteChartRegionDecomposition (M := M)}
  {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}

namespace OrientedGraphPiece

variable (P : D.OrientedGraphPiece e R C a b)

omit [T2Space M] in
theorem endpoints_mem_tube (hab : a ≤ b) :
    P.parameter a ∈ Ioo P.tubeLeft P.tubeRight ∧
      P.parameter b ∈ Ioo P.tubeLeft P.tubeRight := by
  have hab' := P.parameter_strictMono.monotoneOn
    (P.interval_source (left_mem_Icc.mpr hab))
    (P.interval_source (right_mem_Icc.mpr hab)) hab
  exact ⟨⟨P.tube_left_lt, hab'.trans_lt P.tube_right_lt⟩,
    ⟨P.tube_left_lt.trans_le hab', P.tube_right_lt⟩⟩

end OrientedGraphPiece

namespace OrientedEdgeGraphSubdivision

variable (S : D.OrientedEdgeGraphSubdivision e R C a b)

def firstPiece : Fin S.count := ⟨0, S.count_pos⟩

def lastPiece : Fin S.count := ⟨S.count - 1, Nat.sub_lt S.count_pos (by decide)⟩

omit [T2Space M] in
@[simp] theorem firstPiece_castSucc : S.firstPiece.castSucc = 0 := rfl

omit [T2Space M] in
@[simp] theorem lastPiece_succ : S.lastPiece.succ = Fin.last S.count := by
  apply Fin.ext
  change S.count - 1 + 1 = S.count
  have := S.count_pos
  omega



structure CutChain (dLeft dRight : EuclideanSpace ℝ (Fin 2)) where
  direction : Fin (S.count + 1) → EuclideanSpace ℝ (Fin 2)
  separator : ∀ i j : Fin S.count, i.succ = j.castSucc → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ
  first : direction 0 = dLeft
  last : direction (Fin.last S.count) = dRight
  direction_ne_zero : ∀ k, direction k ≠ 0
  left_transverse : ∀ i, 0 < ((S.piece i).frame (direction i.castSucc)).2 -
    deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc)) *
      ((S.piece i).frame (direction i.castSucc)).1
  right_transverse : ∀ i, 0 < ((S.piece i).frame (direction i.succ)).2 -
    deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.succ)) *
      ((S.piece i).frame (direction i.succ)).1
  internal_direction : ∀ (i j : Fin S.count) (_hij : i.succ = j.castSucc),
    direction i.succ = (S.piece i).frame.symm (0, 1)
  separator_zero : ∀ (i j : Fin S.count) (hij : i.succ = j.castSucc), separator i j hij (direction i.succ) = 0
  separator_left_pos : ∀ (i j : Fin S.count) (hij : i.succ = j.castSucc),
    0 < separator i j hij ((S.piece i).frame.symm
      (1, deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.succ))))
  separator_right_pos : ∀ (i j : Fin S.count) (hij : i.succ = j.castSucc),
    0 < separator i j hij ((S.piece j).frame.symm
      (1, deriv (S.piece j).lower ((S.piece j).parameter (S.cut i.succ))))
  internal_ray : ∀ (i j : Fin S.count) (_hij : i.succ = j.castSucc), ∀ᶠ r in 𝓝[>] (0 : ℝ),
    C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • direction i.succ ∈ C.source ∧
    C (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • direction i.succ) ∈
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R

omit [T2Space M] in


theorem exists_cutChain
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (dLeft dRight : EuclideanSpace ℝ (Fin 2))
    (hLeft : 0 < ((S.piece S.firstPiece).frame dLeft).2 -
      deriv (S.piece S.firstPiece).lower ((S.piece S.firstPiece).parameter a) *
        ((S.piece S.firstPiece).frame dLeft).1)
    (hRight : 0 < ((S.piece S.lastPiece).frame dRight).2 -
      deriv (S.piece S.lastPiece).lower ((S.piece S.lastPiece).parameter b) *
        ((S.piece S.lastPiece).frame dRight).1) :
    Nonempty (S.CutChain dLeft dRight) := by
  rcases S with ⟨n, hn, c, hc, hfirst, hlast, hmem, piece⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hLeft' : 0 < ((piece 0).frame dLeft).2 -
      deriv (piece 0).lower ((piece 0).parameter (c 0)) * ((piece 0).frame dLeft).1 := by
    change 0 < ((piece 0).frame dLeft).2 -
      deriv (piece 0).lower ((piece 0).parameter a) * ((piece 0).frame dLeft).1 at hLeft
    have he := congrArg (fun t => deriv (piece 0).lower ((piece 0).parameter t)) hfirst
    rw [he]
    exact hLeft
  have hRight' : 0 < ((piece (Fin.last m)).frame dRight).2 -
      deriv (piece (Fin.last m)).lower ((piece (Fin.last m)).parameter (c (Fin.last (m + 1)))) *
        ((piece (Fin.last m)).frame dRight).1 := by
    change 0 < ((piece (Fin.last m)).frame dRight).2 -
      deriv (piece (Fin.last m)).lower ((piece (Fin.last m)).parameter b) *
        ((piece (Fin.last m)).frame dRight).1 at hRight
    have he := congrArg (fun t => deriv (piece (Fin.last m)).lower
      ((piece (Fin.last m)).parameter t)) hlast
    rw [he]
    exact hRight
  obtain ⟨d, ℓ, hd0, hdlast, hdne, hdpos, hsep⟩ :=
    D.exists_oriented_graph_cut_chain e R C hCinv c hc
      (fun i => (piece i).frame) (fun i => (piece i).parameter) (fun i => (piece i).lower)
      (fun i => (piece i).parameter_smooth) (fun i => (piece i).lower_smooth)
      (fun i => (piece i).interval_source) (fun i => (piece i).graph_source)
      (fun i => (piece i).graph_map) (fun i => (piece i).positive_projection)
      (fun i => (piece i).tubeLeft) (fun i => (piece i).tubeRight) (fun i => (piece i).tubeWidth)
      (fun i => (piece i).tube_width_pos)
      (fun i => (piece i).endpoints_mem_tube (hc Fin.castSucc_lt_succ).le)
      (fun i x hx z hz => ⟨((piece i).tube x hx z hz).1, ((piece i).tube x hx z hz).2.2.1⟩)
      dLeft dRight hLeft' hRight'
  have hadjacent : ∀ i j : Fin (m + 1), i.succ = j.castSucc →
      ∃ l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ,
        d i.succ = (piece i).frame.symm (0, 1) ∧ l (d i.succ) = 0 ∧
        0 < l ((piece i).frame.symm (1, deriv (piece i).lower ((piece i).parameter (c i.succ)))) ∧
        0 < l ((piece j).frame.symm (1, deriv (piece j).lower ((piece j).parameter (c i.succ)))) ∧
        ∀ᶠ r in 𝓝[>] (0 : ℝ),
          C.symm ((D.edge e.1 e.2).map (c i.succ)) + r • d i.succ ∈ C.source ∧
          C (C.symm ((D.edge e.1 e.2).map (c i.succ)) + r • d i.succ) ∈
            connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
    intro i j hij
    have hv : i.val + 1 = j.val := congrArg Fin.val hij
    have hi : i.val < m := by omega
    let k : Fin m := ⟨i.val, hi⟩
    have hik : i = k.castSucc := by apply Fin.ext; rfl
    have hjk : j = k.succ := by apply Fin.ext; exact hv.symm
    rw [hik, hjk]
    exact ⟨ℓ k, hsep k⟩
  choose separator hseparator using hadjacent
  refine ⟨{
    direction := d
    separator := separator
    first := hd0
    last := hdlast
    direction_ne_zero := hdne
    left_transverse := fun i => (hdpos i).1
    right_transverse := fun i => (hdpos i).2
    internal_direction := fun i j hij => (hseparator i j hij).1
    separator_zero := fun i j hij => (hseparator i j hij).2.1
    separator_left_pos := fun i j hij => (hseparator i j hij).2.2.1
    separator_right_pos := fun i j hij => (hseparator i j hij).2.2.2.1
    internal_ray := fun i j hij => (hseparator i j hij).2.2.2.2
  }⟩

end OrientedEdgeGraphSubdivision
end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
