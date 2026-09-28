import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.SmallSimplicialStars
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_subdivision_geometric_mesh (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D) (n : ℕ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      (∀ s ∈ L.faces, s.card ≤ N + 1) ∧
      ∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) ≤
        ((N : ℝ) / ((N : ℝ) + 1)) ^ n * D := by
  classical
  induction n with
  | zero => exact ⟨K, hfinite, IsSubdivision.refl K, hN, by simpa using hdiam⟩
  | succ n ih =>
    obtain ⟨L, hL, hLK, hLN, hLd⟩ := ih
    let : Fintype L.faces := hL.fintype
    refine ⟨L.barycentricSubdivision, L.barycentricSubdivision_finite,
      L.barycentricSubdivision_isSubdivision.trans hLK,
      L.barycentricSubdivision_card_le hLN, ?_⟩
    intro s hs
    have h := L.barycentricSubdivision_diam_le hLN (by positivity) hLd s hs
    simpa only [pow_succ, mul_assoc, mul_left_comm] using h

theorem exists_finite_subdivision_mesh (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      (∀ s ∈ L.faces, s.card ≤ N + 1) ∧
      ∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) ≤ δ := by
  let D := diam K.space
  have hD : 0 ≤ D := diam_nonneg
  have hdiam (s : Finset E) (hs : s ∈ K.faces) :
      diam (convexHull ℝ (s : Set E)) ≤ D :=
    diam_mono (K.convexHull_subset_space hs) (K.isCompact_space_of_finite hfinite).isBounded
  let q : ℝ := (N : ℝ) / ((N : ℝ) + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hlim : Tendsto (fun n : ℕ => q ^ n * D) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const D
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨L, hL, hLK, hLN, hLd⟩ := K.exists_subdivision_geometric_mesh hfinite hN hD hdiam n
  exact ⟨L, hL, hLK, hLN, fun s hs => (hLd s hs).trans hn.le⟩

theorem exists_finite_subdivision_stars [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    {ι : Type*} (U : ι → Set K.space) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : K.space, ∃ i, x ∈ U i) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      ∀ p : E, {p} ∈ L.faces → ∃ i, ∀ x : K.space,
        (x : E) ∈ (L.closedFaceStar {p}).space → x ∈ U i := by
  classical
  obtain ⟨δ, hδ, hstars⟩ := K.exists_mesh_for_subdivision_stars hfinite U hU hcover
  let N := hfinite.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hfinite.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, _, hLd⟩ := K.exists_finite_subdivision_mesh hfinite hN hδ
  exact ⟨L, hL, hLK, hstars L hLK hLd⟩

end Geometry.SimplicialComplex
