import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ThreeDiskChainMap
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)

theorem exists_upper_resolution_disk_map
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
    (hleft : ∀ t : I01, fA (pA t) = τ (((-1, 1), (t : ℝ)) : C3))
    (hright : ∀ t : I01, fC (pC t) = τ (((1, 1), (t : ℝ)) : C3)) :
    ∃ (D : Set P2) (BC : Set EC) (nA : SA ≃ₜ TR) (nS : source ≃ₜ TL)
      (m : (TR ∪ TL : Set P2) ≃ₜ TR) (mC : SC ≃ₜ TL) (g : P2 → X),
      nA.IsFinitePL ∧ nS.IsFinitePL ∧ m.IsFinitePL ∧ mC.IsFinitePL ∧
      IsFinitePLBallPair ℝ BC {aC, bC} ∧ WC ∪ BC = QC ∧ WC ∩ BC = {aC, bC} ∧
      (∀ t : I01,
        (m ⟨nA ⟨pA t, hSA.1 (hWAQ (pA t).property)⟩,
          Or.inl (nA ⟨pA t, hSA.1 (hWAQ (pA t).property)⟩).property⟩ : P2) =
        m ⟨nS ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩,
          Or.inr (nS ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩).property⟩) ∧
      (∀ t : I01,
        (m ⟨nS ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩,
          Or.inr (nS ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩).property⟩ : P2) =
        mC ⟨pC t, hSC.1 (hWCQ (pC t).property)⟩) ∧
      PolyhedralPLInCharts e g (TR ∪ TL) ∧
      (∀ x : SA, g (m ⟨nA x, Or.inl (nA x).property⟩) = fA x) ∧
      (∀ x : source, g (m ⟨nS x, Or.inr (nS x).property⟩) = τ (strip (1 / 4) true x)) ∧
      (∀ x : SC, g (mC x) = fC x) ∧
      g '' (TR ∪ TL) = (fA '' SA ∪ τ '' (strip (1 / 4) true '' source)) ∪ fC '' SC ∧
      IsFinitePLBallPair P2 (TR ∪ TL)
        ((fun x : (TR ∪ TL : Set P2) => (m x : P2)) '' (Subtype.val ⁻¹' D) ∪
         (fun x : SC => (mC x : P2)) '' (Subtype.val ⁻¹' BC)) ∧
      ∀ Z : Set X, (TR ∪ TL) ∩ g ⁻¹' Z =
        ((fun x : SA => (m ⟨nA x, Or.inl (nA x).property⟩ : P2)) ''
          {x : SA | fA x ∈ Z} ∪
         (fun x : source => (m ⟨nS x, Or.inr (nS x).property⟩ : P2)) ''
          {x : source | τ (strip (1 / 4) true x) ∈ Z}) ∪
        (fun x : SC => (mC x : P2)) '' {x : SC | fC x ∈ Z} := by
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
  obtain ⟨_, _, V, D, BC, nA, nS, q, m, mC, g,
      _, _, _, _, _, _, _, _, hqval, _, hBC, _, _, hWCB, hWCBi,
      hnA, hnS, hm, hmC, hseamL, hseamR, _, _, _, hg, hgA, hgS, hgC, him, hball, hpre⟩ :=
    exists_three_disk_chain_map e hcompat hSA hrect hSC hWA hL hR hWC
      hWAQ hLQ hRQ hWCQ hdisj habA hends habC pA pL pR pC hpA hpL hpR hpC
      hpA0 hpA1 (hpLval 0) (hpLval 1) (hpRval 0) (hpRval 1) hpC0 hpC1
      hfA hfS hfC hagreeL hagreeR
  have hparamL (t : I01) :
      (⟨pL t, hrect.1 (hLQ (pL t).property)⟩ : source) =
        ⟨((t : ℝ), -1), ⟨t.property, by norm_num⟩⟩ := Subtype.ext (hpLval t)
  have hparamR (t : I01) :
      (⟨pR t, hrect.1 (hRQ (pR t).property)⟩ : source) =
        ⟨((t : ℝ), 1), ⟨t.property, by norm_num⟩⟩ := Subtype.ext (hpRval t)
  refine ⟨D, BC, nA, nS, m, mC, g, hnA, hnS, hm, hmC, hBC, hWCB, hWCBi,
    ?_, ?_, hg, hgA, hgS, hgC, ?_, hball, hpre⟩
  · intro t
    have h := hseamL t
    rw [hparamL] at h
    exact congrArg (fun z : (TR ∪ TL : Set P2) => (m z : P2)) (Subtype.ext h)
  · intro t
    apply hseamR t
    exact ((hqval t).trans (congrArg (fun z : source => (nS z : P2)) (hparamR t))).symm
  · simpa only [image_image, Function.comp_def] using him

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
