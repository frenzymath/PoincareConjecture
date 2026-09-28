import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.OriginalTube
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
open PolygonalCrossingResolution

def transverseSquare (r : ℝ) : Set P2 := Icc (-r) r ×ˢ Icc (-r) r
def closedTube (r : ℝ) : Set C3 := transverseSquare r ×ˢ Icc 0 1
def openTube (r : ℝ) : Set C3 := interior (transverseSquare r) ×ˢ Icc 0 1
def lateral (r : ℝ) : Set C3 := frontier (transverseSquare r) ×ˢ Icc 0 1
def ends (r : ℝ) : Set C3 := transverseSquare r ×ˢ ({0,1} : Set ℝ)

theorem ends_subset {r : ℝ} : ends r ⊆ closedTube r := by
  intro z hz
  refine ⟨hz.1,?_⟩
  rcases hz.2 with h | h
  · rw [show z.2 = 0 from h]
    norm_num
  · rw [show z.2 = 1 from h]
    norm_num

theorem closedTube_subset {r : ℝ} (hr : r ≤ 1) : closedTube r ⊆ tube := by
  intro z hz
  exact ⟨⟨⟨by linarith [hz.1.1.1],by linarith [hz.1.1.2]⟩,
    ⟨by linarith [hz.1.2.1],by linarith [hz.1.2.2]⟩⟩,hz.2⟩

theorem isClosed_transverseSquare (r : ℝ) : IsClosed (transverseSquare r) :=
  isClosed_Icc.prod isClosed_Icc

theorem openTube_subset (r : ℝ) : openTube r ⊆ closedTube r :=
  prod_mono interior_subset Subset.rfl

theorem lateral_subset (r : ℝ) : lateral r ⊆ closedTube r :=
  prod_mono (isClosed_transverseSquare r).frontier_subset Subset.rfl

theorem isCompact_closedTube (r : ℝ) : IsCompact (closedTube r) :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

theorem isCompact_lateral (r : ℝ) : IsCompact (lateral r) :=
  ((isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_frontier
    (isClosed_transverseSquare r).frontier_subset).prod isCompact_Icc

theorem closedTube_sdiff_openTube (r : ℝ) : closedTube r \ openTube r = lateral r := by
  rw [lateral,frontier,(isClosed_transverseSquare r).closure_eq]
  ext z
  simp only [closedTube,openTube,mem_sdiff,mem_prod]
  tauto

theorem closedTube_sdiff_lateral (r : ℝ) : closedTube r \ lateral r = openTube r := by
  rw [← closedTube_sdiff_openTube]
  exact sdiff_sdiff_cancel_left (openTube_subset r)

theorem frontier_closedTube {r : ℝ} (hr : 0 < r) :
    frontier (closedTube r) = lateral r ∪ ends r := by
  rw [closedTube,frontier_prod_eq,(isClosed_transverseSquare r).closure_eq,
    isClosed_Icc.closure_eq,frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  exact union_comm _ _

theorem isFinitePLBallPair_closedTube {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair C3 (closedTube r) (lateral r ∪ ends r) := by
  have hI := isFinitePLBallPair_Icc (show -r < r by linarith)
  have h := (hI.prod hI).prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  have hfront : frontier (closedTube r) = _ := h.frontier_eq_of_finrank_eq rfl
  rw [frontier_closedTube hr] at hfront
  exact hfront.symm ▸ h

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
