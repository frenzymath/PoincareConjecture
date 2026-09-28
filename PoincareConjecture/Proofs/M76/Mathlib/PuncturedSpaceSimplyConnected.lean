import PoincareConjecture.Proofs.M76.Mathlib.FiniteAvoidingApex
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPathSubdivision
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected












set_option autoImplicit false

open Set Metric
open scoped unitInterval

namespace Path






theorem homotopic_refl_in_punctured_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E)
    (x : ({0}ᶜ : Set E)) (p : Path x x) : p.Homotopic (.refl x) := by
  classical
  let U : Set E := {0}ᶜ
  obtain ⟨n, t, S, ht0, htn, _, hS⟩ :=
    p.exists_convex_subpath_partition isClosed_singleton.isOpen_compl
  let a : Fin (n + 2) → U := fun i => p (t i)
  have haL (i : Fin (n + 1)) : (a i.castSucc : E) ∈ S i := by
    simpa only [Path.source] using (hS i).2.2 0
  have haR (i : Fin (n + 1)) : (a i.succ : E) ∈ S i := by
    simpa only [Path.target] using (hS i).2.2 1
  have hseg (i : Fin (n + 1)) :
      segment ℝ (a i.castSucc : E) (a i.succ : E) ⊆ U :=
    ((hS i).1.segment_subset (haL i) (haR i)).trans (hS i).2.1
  obtain ⟨y, hy0, hy⟩ := Submodule.exists_ne_zero_forall_notMem_span_pair hdim
    (fun i : Fin (n + 2) × Fin (n + 2) => (a i.1 : E))
    (fun i : Fin (n + 2) × Fin (n + 2) => (a i.2 : E))
  let Y : U := ⟨y, hy0⟩
  have hradial (i : Fin (n + 2)) : segment ℝ y (a i : E) ⊆ U := by
    have hedge : (0 : E) ∉ segment ℝ (a i : E) (a i : E) := by
      rw [segment_same]
      intro hzero
      exact (a i).property (mem_singleton_iff.mp hzero).symm
    have htriangle := zero_notMem_convexHull_triple_of_notMem_span_pair
      hedge (hy (i, i))
    have hzero : (0 : E) ∉ segment ℝ y (a i : E) := by
      rw [show ({y, (a i : E), (a i : E)} : Set E) = {y, (a i : E)} by
        ext z
        simp, convexHull_pair] at htriangle
      exact htriangle
    intro z hz
    change z ≠ 0
    intro hz0
    exact hzero (hz0 ▸ hz)
  let r : (i : Fin (n + 2)) → Path Y (a i) :=
    fun i => Path.segmentIn U Y (a i) (hradial i)
  let T : Fin (n + 1) → Set E :=
    fun i => convexHull ℝ ({y, (a i.castSucc : E), (a i.succ : E)} : Set E)
  have hTU (i : Fin (n + 1)) : T i ⊆ U := by
    have hzero : (0 : E) ∉ T i := zero_notMem_convexHull_triple_of_notMem_span_pair
      (fun hz => hseg i hz rfl) (hy (i.castSucc, i.succ))
    intro z hz
    change z ≠ 0
    intro hz0
    exact hzero (hz0 ▸ hz)
  have hTy (i : Fin (n + 1)) : y ∈ T i := subset_convexHull ℝ _ (by simp)
  have hTL (i : Fin (n + 1)) : (a i.castSucc : E) ∈ T i :=
    subset_convexHull ℝ _ (by simp)
  have hTR (i : Fin (n + 1)) : (a i.succ : E) ∈ T i :=
    subset_convexHull ℝ _ (by simp)
  have hpieces (i : Fin (n + 1)) :
      (p.subpath (t i.castSucc) (t i.succ)).Homotopic
        ((r i.castSucc).symm.trans (r i.succ)) := by
    let e := Path.segmentIn U (a i.castSucc) (a i.succ) (hseg i)
    have hfirst : (p.subpath (t i.castSucc) (t i.succ)).Homotopic e :=
      Path.homotopic_of_convex_range (hS i).1 (hS i).2.1 _ _ (hS i).2.2
        (fun u => Path.segmentIn_mem_convex (hS i).1 _ _ _ (haL i) (haR i) u)
    refine hfirst.trans (Path.homotopic_of_convex_range (convex_convexHull ℝ _)
      (hTU i) _ _ ?_ ?_)
    · intro u
      exact Path.segmentIn_mem_convex (convex_convexHull ℝ _) _ _ _ (hTL i) (hTR i) u
    · intro u
      have hu : ((r i.castSucc).symm.trans (r i.succ)) u ∈
          range (r i.castSucc) ∪ range (r i.succ) := by
        rw [← Path.symm_range (r i.castSucc), ← Path.trans_range]
        exact mem_range_self u
      rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
      · rw [← hv]
        exact Path.segmentIn_mem_convex (convex_convexHull ℝ _) _ _ _ (hTy i) (hTL i) v
      · rw [← hv]
        exact Path.segmentIn_mem_convex (convex_convexHull ℝ _) _ _ _ (hTy i) (hTR i) v
  have hcontract := Path.Homotopic.concat_radial a Y r
    (fun i => p.subpath (t i.castSucc) (t i.succ)) hpieces
  have hconcat := Path.Homotopic.concat_subpath p t
  have h := hconcat.symm.trans hcontract
  have h0 : x = a 0 := by simp [a, ht0]
  have hn : x = a (Fin.last (n + 1)) := by simp [a, htn]
  let r0 : Path Y x := (r 0).cast rfl h0
  have hend : (r (Fin.last (n + 1))).cast rfl hn = r0 := by
    ext u
    change AffineMap.lineMap y (a (Fin.last (n + 1)) : E) (u : ℝ) =
      AffineMap.lineMap y (a 0 : E) (u : ℝ)
    rw [← hn, ← h0]
  have hleft : (p.subpath (t 0) (t (Fin.last (n + 1)))).cast h0 hn = p := by
    ext u
    simp only [Path.cast_coe, Path.subpath, Path.coe_mk_mk, ht0, htn,
      Icc.convexComb_zero_one, Function.comp_apply]
  have hright : ((r 0).symm.trans (r (Fin.last (n + 1)))).cast h0 hn =
      r0.symm.trans r0 := by
    rw [Path.cast_trans _ _ h0 rfl hn, Path.cast_symm, hend]
  have hbased := h.pathCast h0 hn
  rw [hleft, hright] at hbased
  exact hbased.trans (Path.Homotopic.symm_trans r0)

end Path





theorem isSimplyConnected_compl_zero_of_two_lt_finrank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E) :
    IsSimplyConnected ({0}ᶜ : Set E) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  constructor
  · apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  · exact Path.homotopic_refl_in_punctured_space hdim
