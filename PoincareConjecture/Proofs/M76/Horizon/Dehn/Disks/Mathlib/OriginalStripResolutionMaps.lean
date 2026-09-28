import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripExteriorDisks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.UpperResolutionDiskMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionDiskMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.TubeArmOrientation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

theorem polyhedralPL_restrict_disk
    {E F X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X F}
    {S A B : Set E} {f : E → X} (hf : PolyhedralPLInCharts e f S)
    (hA : IsFinitePLBallPair P2 A B) (hAS : A ⊆ S) :
    PolyhedralPLInCharts e f A := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hA
  simpa only [hKs] using hf.restrict_finite K hK (hKs.subset.trans hAS)

theorem exists_original_strip_resolution_maps
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
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1)) :
    ∃ (A M C : Set E) (s0 s1 : Bool) (RU RV : Set P2) (gU gV : P2 → X)
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
      IsFinitePLBallPair P2 T RU ∧ IsFinitePLBallPair P2 T RV ∧
      PolyhedralPLInCharts e gU T ∧ PolyhedralPLInCharts e gV T ∧
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
      (∀ Z : Set X, T ∩ gU ⁻¹' Z =
        (jUA '' {x : A | f x ∈ Z} ∪ jUS '' {x : source | τ' (strip (1 / 4) true x) ∈ Z}) ∪
          jUC '' {x : C | f x ∈ Z}) ∧
      (∀ Z : Set X, T ∩ gV ⁻¹' Z =
        (((jVA '' {x : A | f x ∈ Z} ∪
          jVL '' {x : source | τ' (alternate (1 / 4) false x) ∈ Z}) ∪
          jVM '' {x : M | f x ∈ Z}) ∪
          jVR '' {x : source | τ' (alternate (1 / 4) true x) ∈ Z}) ∪
          jVC '' {x : C | f x ∈ Z}) := by
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
  obtain ⟨DU, BCU, nAU, nSU, mU, nCU, gU, _, _, _, _, _, _, _, _, _,
      hgU, hgUA, hgUS, hgUC, himU, hballU, hpreU⟩ :=
    exists_upper_resolution_disk_map e hcompat hA hC hWA hWC
      subset_union_right subset_union_right habA habC pA pC hpA hpC
      (hpAval 0) (hpAval 1) (hpCval 0) (hpCval 1) hfA hfC hτ' hAeq hCeq
  obtain ⟨DV, BCV, nAV, nLV, mLV, nMV, nAMLV, nRV, mRV, nCV, gV, hdata⟩ :=
    exists_alternate_resolution_disk_map e hcompat hA hM hC hWA hLM hRM hWC
      subset_union_right subset_union_right (subset_union_right.trans subset_union_left)
      subset_union_right hLMRM habA habL habC pA pL pR pC hpA hpL hpR hpC
      (hpAval 0) (hpAval 1) (hpLval 0) (hpLval 1) (hpRval 0) (hpRval 1)
      (hpCval 0) (hpCval 1) hfA hfM hfC hτ' hAeq hLeq hReq hCeq
  dsimp only at hdata
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgV,
      hgVA, hgVL, hgVM, hgVR, hgVC, himV, hballV, hpreV, _⟩ := hdata
  exact ⟨A, M, C, s0, s1, _, _, gU, gV,
    (fun x => (mU ⟨nAU x, Or.inl (nAU x).property⟩ : P2)),
    (fun x => (mU ⟨nSU x, Or.inr (nSU x).property⟩ : P2)),
    (fun x => (nCU x : P2)),
    (fun x => (mRV ⟨nAMLV ⟨mLV ⟨nAV x, Or.inl (nAV x).property⟩,
      Or.inl (mLV ⟨nAV x, Or.inl (nAV x).property⟩).property⟩,
      Or.inl (nAMLV _).property⟩ : P2)),
    (fun x => (mRV ⟨nAMLV ⟨mLV ⟨nLV x, Or.inr (nLV x).property⟩,
      Or.inl (mLV ⟨nLV x, Or.inr (nLV x).property⟩).property⟩,
      Or.inl (nAMLV _).property⟩ : P2)),
    (fun x => (mRV ⟨nAMLV ⟨nMV x, Or.inr (nMV x).property⟩,
      Or.inl (nAMLV _).property⟩ : P2)),
    (fun x => (mRV ⟨nRV x, Or.inr (nRV x).property⟩ : P2)),
    (fun x => (nCV x : P2)),
    hA, hM, hC, hAM, hMC, hAC, hcover, hballU, hballV, hgU, hgV,
    hgUA, hgUS, hgUC, hgVA, hgVL, hgVM, hgVR, hgVC, himU, himV, hpreU, hpreV⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
