import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.OriginalStripResolutionMaps
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.MarkedUpperResolution
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.MarkedAlternateResolution

/-!
# Proper resolution maps constructed from the original strip neighborhood

Construct the exterior disks, their prescribed arm charts, the required tube
orientation and all marked attachment equations from the original source disk.
Both resulting disk rims are exactly their target-frontier preimages.
See Dehn039, sections 2--6, and Hatcher, section 3.1, printed pp. 56--57.
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

/-- The original source strips and tube construct both resolution maps with
their complete frontier preimages. No exterior decomposition, arm chart,
marked attachment, or candidate map is supplied as an additional premise. -/
theorem exists_original_strip_proper_resolution_maps
    {E F X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q)
    (c : Bool → P2 → E) (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    {f : E → X} (hf : PolyhedralPLInCharts e f S)
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (Z : Set X) (hfZ : ∀ x ∈ S, f x ∈ Z ↔ x ∈ Q)
    (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ (A M C : Set E) (s0 s1 : Bool) (gU gV : P2 → X)
      (jUA : A → P2) (jUS : source → P2) (jUC : C → P2)
      (jVA : A → P2) (jVL : source → P2) (jVM : M → P2)
      (jVR : source → P2) (jVC : C → P2),
      let τ' := τ ∘ tubeArmOrientation s0 s1
      IsFinitePLBallPair P2 A ((A ∩ Q) ∪ c false '' arm (farArmParameter (!s0))) ∧
      IsFinitePLBallPair P2 M (((M ∩ Q) ∪ c false '' arm (farArmParameter s0)) ∪
        c true '' arm (farArmParameter s1)) ∧
      IsFinitePLBallPair P2 C ((C ∩ Q) ∪ c true '' arm (farArmParameter (!s1))) ∧
      Disjoint A M ∧ Disjoint M C ∧ Disjoint A C ∧
      ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S ∧
      PolyhedralPLInCharts e gU T ∧ PolyhedralPLInCharts e gV T ∧
      IsFinitePLBallPair P2 T (T ∩ gU ⁻¹' Z) ∧
      IsFinitePLBallPair P2 T (T ∩ gV ⁻¹' Z) ∧
      (∀ x : A, gU (jUA x) = f x) ∧
      (∀ x : source, gU (jUS x) = τ' (strip (1 / 4) true x)) ∧
      (∀ x : C, gU (jUC x) = f x) ∧
      (∀ x : A, gV (jVA x) = f x) ∧
      (∀ x : source, gV (jVL x) = τ' (alternate (1 / 4) false x)) ∧
      (∀ x : M, gV (jVM x) = f x) ∧
      (∀ x : source, gV (jVR x) = τ' (alternate (1 / 4) true x)) ∧
      (∀ x : C, gV (jVC x) = f x) ∧
      gU '' T = (f '' A ∪ τ' '' (strip (1 / 4) true '' source)) ∪ f '' C ∧
      gV '' T = (((f '' A ∪ τ' '' (alternate (1 / 4) false '' source)) ∪ f '' M) ∪
        τ' '' (alternate (1 / 4) true '' source)) ∪ f '' C ∧
      (∀ U : Set X, T ∩ gU ⁻¹' U =
        (jUA '' {x : A | f x ∈ U} ∪ jUS '' {x : source | τ' (strip (1 / 4) true x) ∈ U}) ∪
          jUC '' {x : C | f x ∈ U}) ∧
      (∀ U : Set X, T ∩ gV ⁻¹' U =
        (((jVA '' {x : A | f x ∈ U} ∪
          jVL '' {x : source | τ' (alternate (1 / 4) false x) ∈ U}) ∪
          jVM '' {x : M | f x ∈ U}) ∪
          jVR '' {x : source | τ' (alternate (1 / 4) true x) ∈ U}) ∪
          jVC '' {x : C | f x ∈ U}) := by
  obtain ⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
      _, _, _, _, _, _⟩ := exists_strip_exterior_disks hS c hcPL hci hcS hcQ hdisj
  have hAS : A ⊆ S := fun x hx => hcover.subset (Or.inl (Or.inl (Or.inl hx)))
  have hMS : M ⊆ S := fun x hx => hcover.subset (Or.inl (Or.inl (Or.inr hx)))
  have hCS : C ⊆ S := fun x hx => hcover.subset (Or.inl (Or.inr hx))
  have hfA := polyhedralPL_restrict_disk hf hA hAS
  have hfM := polyhedralPL_restrict_disk hf hM hMS
  have hfC := polyhedralPL_restrict_disk hf hC hCS
  have hfar (s : Bool) : farArmParameter s ∈ Icc (-1 : ℝ) 1 := by
    cases s <;> norm_num [farArmParameter]
  obtain ⟨hWA, habA, pA, hpA, hpAval⟩ :=
    exists_embedded_strip_arm_parameter (c false) (hcPL false) (hci false)
      (farArmParameter (!s0)) (hfar (!s0))
  obtain ⟨hLM, habL, pL, hpL, hpLval⟩ :=
    exists_embedded_strip_arm_parameter (c true) (hcPL true) (hci true)
      (farArmParameter s1) (hfar s1)
  obtain ⟨hRM, _, pR, hpR, hpRval⟩ :=
    exists_embedded_strip_arm_parameter (c false) (hcPL false) (hci false)
      (farArmParameter s0) (hfar s0)
  obtain ⟨hWC, habC, pC, hpC, hpCval⟩ :=
    exists_embedded_strip_arm_parameter (c true) (hcPL true) (hci true)
      (farArmParameter (!s1)) (hfar (!s1))
  have hLMRM := hdisj.symm.mono (image_mono (arm_far_subset_source s1))
    (image_mono (arm_far_subset_source s0))
  let τ' := τ ∘ tubeArmOrientation s0 s1
  have hτ' : PolyhedralPLInCharts e τ' tube := reoriented_tube_polyhedralPL e hτ s0 s1
  have hτ'Z := reoriented_tube_frontier_iff τ hτZ s0 s1
  have hcorners := reoriented_tube_old_arm_equations f (c false) (c true) τ h0 h1 s0 s1
  have hAeq (t : I01) : f (pA t) = τ' ((-1, 1), t) := by
    rw [hpAval]
    exact (hcorners t).1
  have hLeq (t : I01) : f (pL t) = τ' ((-1, -1), t) := by
    rw [hpLval]
    exact (hcorners t).2.1
  have hReq (t : I01) : f (pR t) = τ' ((1, -1), t) := by
    rw [hpRval]
    exact (hcorners t).2.2.1
  have hCeq (t : I01) : f (pC t) = τ' ((1, 1), t) := by
    rw [hpCval]
    exact (hcorners t).2.2.2
  have hAQ := retained_piece_frontier_preimage f hfZ hAS
  have hMQ := retained_piece_frontier_preimage f hfZ hMS
  have hCQ := retained_piece_frontier_preimage f hfZ hCS
  have hmark (i s : Bool) := original_strip_arm_frontier_inter f (c i) hfZ
    (hcS i) (hcQ i) (farArmParameter s) (hfar s)
  obtain ⟨gU, jUA, jUS, jUC, hgU, hballU, hgUA, hgUS, hgUC, himU, hpreU⟩ :=
    exists_marked_upper_resolution_disk_map e hcompat hA hC hWA hWC
      subset_union_right subset_union_right habA habC pA pC hpA hpC
      (hpAval 0) (hpAval 1) (hpCval 0) (hpCval 1) hfA hfC hτ' hAeq hCeq
      Z hτ'Z (by rw [hAQ]) (by rw [hCQ]) (hmark false (!s0)) (hmark true (!s1))
  obtain ⟨nAV, nLV, mLV, nMV, nAMLV, nRV, mRV, nCV, gV, hdata⟩ :=
    exists_marked_alternate_resolution_disk_map e hcompat hA hM hC hWA hLM hRM hWC
      subset_union_right subset_union_right (subset_union_right.trans subset_union_left)
      subset_union_right hLMRM habA habL habC pA pL pR pC hpA hpL hpR hpC
      (hpAval 0) (hpAval 1) (hpLval 0) (hpLval 1) (hpRval 0) (hpRval 1)
      (hpCval 0) (hpCval 1) hfA hfM hfC hτ' hAeq hLeq hReq hCeq
      Z hτ'Z (by rw [hAQ]) (by rw [hMQ]) (by rw [hCQ])
      (hmark false (!s0)) (hmark true s1) (hmark false s0) (hmark true (!s1))
  dsimp only at hdata
  obtain ⟨_, _, _, _, _, _, _, _, hgV, hgVA, hgVL, hgVM, hgVR, hgVC,
    himV, hballV, hpreV⟩ := hdata
  exact ⟨A, M, C, s0, s1, gU, gV, jUA, jUS, jUC, _, _, _, _, _,
    hA, hM, hC, hAM, hMC, hAC, hcover, hgU, hgV, hballU, hballV,
    hgUA, hgUS, hgUC, hgVA, hgVL, hgVM, hgVR, hgVC, himU, himV, hpreU, hpreV⟩

end PoincareMT.M76.Dehn.PolygonalCrossingResolution
