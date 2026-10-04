import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.MarkedDiskChain
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.ResolutionStripBoundary
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.PolygonalStripDiskAttachment

/-!
# The complete frontier of the upper resolution disk

Apply the marked attachment construction to the explicit upper strip and
the two original exterior disks. The longitudinal tube condition supplies
the exact strip frontier preimage. See Dehn039, sections 5--6.
-/

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareMT.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

/-- Construct the upper resolution map with its entire frontier preimage,
retaining both exterior maps, the complete replacement strip, and all target
preimages. The old tube and original exterior boundary equations are the inputs. -/
theorem exists_marked_upper_resolution_disk_map
    {EA EC F X ι : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {SA QA WA : Set EA} {SC QC WC : Set EC} {aA bA : EA} {aC bC : EC}
    (hSA : IsFinitePLBallPair P2 SA QA) (hSC : IsFinitePLBallPair P2 SC QC)
    (hWA : IsFinitePLBallPair ℝ WA {aA, bA})
    (hWC : IsFinitePLBallPair ℝ WC {aC, bC})
    (hWAQ : WA ⊆ QA) (hWCQ : WC ⊆ QC) (habA : aA ≠ bA) (habC : aC ≠ bC)
    (pA : I01 ≃ₜ WA) (pC : I01 ≃ₜ WC) (hpA : pA.IsFinitePL) (hpC : pC.IsFinitePL)
    (hpA0 : (pA (0 : unitInterval) : EA) = aA)
    (hpA1 : (pA (1 : unitInterval) : EA) = bA)
    (hpC0 : (pC (0 : unitInterval) : EC) = aC)
    (hpC1 : (pC (1 : unitInterval) : EC) = bC)
    {fA : EA → X} {fC : EC → X} {τ : C3 → X}
    (hfA : PolyhedralPLInCharts e fA SA) (hfC : PolyhedralPLInCharts e fC SC)
    (hτ : PolyhedralPLInCharts e τ tube)
    (hleft : ∀ t : I01, fA (pA t) = τ ((-1, 1), t))
    (hright : ∀ t : I01, fC (pC t) = τ ((1, 1), t))
    (Z : Set X) (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA) (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA}) (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (g : P2 → X) (jA : SA → P2) (jS : source → P2) (jC : SC → P2),
      PolyhedralPLInCharts e g T ∧ IsFinitePLBallPair P2 T (T ∩ g ⁻¹' Z) ∧
      (∀ x : SA, g (jA x) = fA x) ∧
      (∀ x : source, g (jS x) = τ (strip (1 / 4) true x)) ∧
      (∀ x : SC, g (jC x) = fC x) ∧
      g '' T = (fA '' SA ∪ τ '' (strip (1 / 4) true '' source)) ∪ fC '' SC ∧
      ∀ U : Set X, T ∩ g ⁻¹' U =
        (jA '' {x : SA | fA x ∈ U} ∪
          jS '' {x : source | τ (strip (1 / 4) true x) ∈ U}) ∪
          jC '' {x : SC | fC x ∈ U} := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  have hrect : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨hL, pL, hpL, hpLval⟩ := exists_arm_parameter (-1)
  obtain ⟨hR, pR, hpR, hpRval⟩ := exists_arm_parameter 1
  have hLQ : arm (-1) ⊆ stripRim := fun _ hx => Or.inr ⟨hx.1, Or.inl hx.2⟩
  have hRQ : arm 1 ⊆ stripRim := fun _ hx => Or.inr ⟨hx.1, Or.inr hx.2⟩
  have hdisj : Disjoint (arm (-1)) (arm 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hneg : x.2 = -1 := hx.2
    have hpos : x.2 = 1 := hy.2
    linarith
  have hends : ((0, -1) : P2) ≠ (1, -1) := by
    intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst h
    norm_num at h01
  have hs := (finitePiecewiseAffineOn_maps (1 / 4) true).1
  have hsCopy := hs
  obtain ⟨K, hK, hKs, _⟩ := hsCopy
  have hfS : PolyhedralPLInCharts e (τ ∘ strip (1 / 4) true) source := by
    have hreg : FinitePiecewiseAffineOn (strip (1 / 4) true) K.space := by
      simpa only [hKs] using hs
    have hmap : MapsTo (strip (1 / 4) true) K.space tube := by
      simpa only [hKs] using (mapsTo_tube hb.le true).1
    simpa only [hKs] using hτ.comp_finitePiecewiseAffineOn K hK hreg hmap
  have hagreeL (t : I01) : fA (pA t) = (τ ∘ strip (1 / 4) true) (pL t) := by
    change fA (pA t) = τ (strip (1 / 4) true (pL t))
    rw [hpLval, (arm_endpoints hb (t : ℝ)).1]
    exact hleft t
  have hagreeR (t : I01) : (τ ∘ strip (1 / 4) true) (pR t) = fC (pC t) := by
    change τ (strip (1 / 4) true (pR t)) = fC (pC t)
    rw [hpRval, (arm_endpoints hb (t : ℝ)).2.1]
    exact (hright t).symm
  have hQS : stripRim =
      ((source ∩ (τ ∘ strip (1 / 4) true) ⁻¹' Z) ∪ arm 1) ∪ arm (-1) := by
    have hpre : source ∩ (τ ∘ strip (1 / 4) true) ⁻¹' Z = stripEnds :=
      resolution_strip_frontier_preimage τ hτZ hb.le false true
    rw [hpre]
    rw [stripRim_eq_ends_union_arms]
    ac_rfl
  have hmarkL := resolution_strip_arm_frontier_inter τ hτZ hb.le
    (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) false true
  have hmarkR := resolution_strip_arm_frontier_inter τ hτZ hb.le
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) false true
  obtain ⟨nA, nS, m, nC, g, _, _, _, _, _, _, hg, hgA, hgS, hgC,
    him, hball, hpre⟩ := exists_three_piece_marked_disk_map e hcompat hSA hrect hSC
      hWA hL hR hWC hWAQ hLQ hRQ hWCQ hdisj habA hends habC
      pA pL pR pC hpA hpL hpR hpC hpA0 hpA1 (hpLval 0) (hpLval 1)
      (hpRval 0) (hpRval 1) hpC0 hpC1 hfA hfS hfC hagreeL hagreeR
      Z hQA hQS hQC hmarkA hmarkL hmarkR hmarkC
  refine ⟨g, _, _, _, hg, hball, hgA, hgS, hgC, ?_, hpre⟩
  simpa only [image_image, Function.comp_def] using him

end PoincareMT.M76.Dehn.PolygonalCrossingResolution
