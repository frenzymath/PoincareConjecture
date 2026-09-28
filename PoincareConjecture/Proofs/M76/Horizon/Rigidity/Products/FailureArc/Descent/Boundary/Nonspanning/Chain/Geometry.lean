import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Boundary.Data
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source

structure NonspanningChainGeometry (SA SM SC : Set P2)
    (pA pL pR pC : I01 → P2) where
  nA : SA ≃ₜ TR
  nL : Strip ≃ₜ TL
  mL : T ≃ₜ TR
  nM : SM ≃ₜ TL
  nAML : T ≃ₜ TR
  nR : Strip ≃ₜ TL
  mR : T ≃ₜ TR
  nC : SC ≃ₜ TL
  pl_nA : nA.IsFinitePL
  pl_nL : nL.IsFinitePL
  pl_mL : mL.IsFinitePL
  pl_nM : nM.IsFinitePL
  pl_nAML : nAML.IsFinitePL
  pl_nR : nR.IsFinitePL
  pl_mR : mR.IsFinitePL
  pl_nC : nC.IsFinitePL
  pR_mem : ∀ t : I01, pR t ∈ SM
  fiberAL : ∀ (x : SA) (y : Strip), (nA x : P2) = nL y ↔
    ∃ t : I01, (x : P2) = pA t ∧ (y : P2) = ((t : ℝ), 1)
  fiberM : ∀ (x : T) (y : SM), (mL x : P2) = nM y ↔
    ∃ t : I01, (x : P2) = nL ⟨((t : ℝ), -1), t.property, by norm_num⟩ ∧
      (y : P2) = pL t
  fiberR : ∀ (x : T) (y : Strip), (nAML x : P2) = nR y ↔
    ∃ t : I01, (x : P2) = nM ⟨pR t, pR_mem t⟩ ∧
      (y : P2) = ((t : ℝ), -1)
  fiberC : ∀ (x : T) (y : SC), (mR x : P2) = nC y ↔
    ∃ t : I01, (x : P2) = nR ⟨((t : ℝ), 1), t.property, by norm_num⟩ ∧
      (y : P2) = pC t
  boundary : NonspanningChainBoundaryData pA pL pR pC nA nL mL nM nAML nR mR nC pR_mem

private theorem constant_auxiliary_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    PolyhedralPLInCharts (fun _ : Unit => OpenPartialHomeomorph.refl ℝ)
      (fun _ : E => (0 : ℝ)) K.space := by
  refine ⟨continuousOn_const, fun x => ?_⟩
  refine ⟨(), K, univ, hK, Subset.rfl, isOpen_univ, mem_univ x, ?_, ?_, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.property
  · exact fun _ _ => mem_univ _
  · exact ⟨K, hK, rfl, K.affineOnFaces_affine (ContinuousAffineMap.const ℝ E 0)⟩

theorem nonempty_nonspanningChainGeometry
    {SA QA WA SM QM LM RM SC QC WC : Set P2}
    {aA bA aL bL aR bR aC bC : P2}
    (hSA : IsFinitePLBallPair P2 SA QA) (hSM : IsFinitePLBallPair P2 SM QM)
    (hSC : IsFinitePLBallPair P2 SC QC)
    (hWA : IsFinitePLBallPair ℝ WA {aA, bA})
    (hLM : IsFinitePLBallPair ℝ LM {aL, bL})
    (hRM : IsFinitePLBallPair ℝ RM {aR, bR})
    (hWC : IsFinitePLBallPair ℝ WC {aC, bC})
    (hWAQ : WA ⊆ QA) (hLMQ : LM ⊆ QM) (hRMQ : RM ⊆ QM) (hWCQ : WC ⊆ QC)
    (hdisj : Disjoint LM RM) (habA : aA ≠ bA) (habL : aL ≠ bL) (habC : aC ≠ bC)
    (pA : I01 ≃ₜ WA) (pL : I01 ≃ₜ LM) (pR : I01 ≃ₜ RM) (pC : I01 ≃ₜ WC)
    (hpA : pA.IsFinitePL) (hpL : pL.IsFinitePL)
    (hpR : pR.IsFinitePL) (hpC : pC.IsFinitePL)
    (hpA0 : (pA (0 : unitInterval) : P2) = aA)
    (hpA1 : (pA (1 : unitInterval) : P2) = bA)
    (hpL0 : (pL (0 : unitInterval) : P2) = aL)
    (hpL1 : (pL (1 : unitInterval) : P2) = bL)
    (hpR0 : (pR (0 : unitInterval) : P2) = aR)
    (hpR1 : (pR (1 : unitInterval) : P2) = bR)
    (hpC0 : (pC (0 : unitInterval) : P2) = aC)
    (hpC1 : (pC (1 : unitInterval) : P2) = bC) :
    Nonempty (NonspanningChainGeometry SA SM SC
      (fun t => pA t) (fun t => pL t) (fun t => pR t) (fun t => pC t)) := by
  let e := fun _ : Unit => OpenPartialHomeomorph.refl ℝ
  have he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid ℝ := by
    intro i j
    change (OpenPartialHomeomorph.refl ℝ).trans (OpenPartialHomeomorph.refl ℝ) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans]
      using (piecewiseAffineGroupoid ℝ).id_mem
  have hconst {S Q : Set P2} (hS : IsFinitePLBallPair P2 S Q) :
      PolyhedralPLInCharts e (fun _ : P2 => (0 : ℝ)) S := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hS
    exact hKs ▸ constant_auxiliary_charts K hK
  have hbox := ((isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  have hτ : PolyhedralPLInCharts e (fun _ : (P2 × ℝ) => (0 : ℝ))
      PolygonalCrossingResolution.tube := by
    simpa only [hKs, PolygonalCrossingResolution.tube] using constant_auxiliary_charts K hK
  obtain ⟨D, BC, nA, nL, mL, nM, nAML, nR, mR, nC, g,
    hnA, hnL, hmL, hnM, hnAML, hnR, hmR, hnC,
    _, hWCB, hWCBi, _, _, _, _, _, _, _, _, _, _, _, hwhole, _, hextra⟩ :=
    PolygonalCrossingResolution.exists_alternate_resolution_disk_map e he
      hSA hSM hSC hWA hLM hRM hWC hWAQ hLMQ hRMQ hWCQ hdisj habA habL habC
      pA pL pR pC hpA hpL hpR hpC hpA0 hpA1 hpL0 hpL1 hpR0 hpR1 hpC0 hpC1
      (hconst hSA) (hconst hSM) (hconst hSC) hτ
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨BA, BL, D1, BAML, BR, V1, V, V2, BM, q1, q, q2,
    _, _, _, hWAB, hWABi, hplusBL, hplusBLi, hV1, hq1, hV1D1, hV1D1i,
    hLMB, hLMBi, hV, hq, hVBAML, hVBAMLi, hminusBR, hminusBRi, hV2, hq2, hV2D, hV2Di,
    hfAL, hfM, _, hfR, hfC, _⟩ := hextra
  refine ⟨⟨nA, nL, mL, nM, nAML, nR, mR, nC,
    hnA, hnL, hmL, hnM, hnAML, hnR, hmR, hnC,
    fun t => hSM.1 (hRMQ (pR t).property), hfAL, ?_, ?_, ?_, ?_⟩⟩
  · intro x y
    simpa only [hq1] using hfM x y
  · intro x y
    simpa only [hq] using hfR x y
  · intro x y
    simpa only [hq2] using hfC x y
  · have hrange {W : Set P2} (p : I01 ≃ₜ W) : range (fun t => (p t : P2)) = W := by
      ext x
      exact ⟨fun ⟨t, ht⟩ => ht ▸ (p t).property,
        fun hx => ⟨p.symm ⟨x, hx⟩, congrArg Subtype.val (p.apply_symm_apply _)⟩⟩
    refine ⟨BA, BL, D1, BM, BAML, BR, D, BC, V1, V, V2,
      (fun t => q1 t), (fun t => q t), (fun t => q2 t), ?_, ?_, hplusBL, hplusBLi,
      hV1, hq1, hV1D1, hV1D1i, ?_, ?_, ?_, hq, hVBAML, hVBAMLi,
      hminusBR, hminusBRi, hV2, hq2, hV2D, hV2Di, ?_, ?_, ?_⟩
    · simpa only [hrange, hSA.frontier_eq_of_finrank_eq rfl] using hWAB
    · simpa only [hrange, hpA0, hpA1] using hWABi
    · simpa only [hrange, hSM.frontier_eq_of_finrank_eq rfl] using hLMB
    · simpa only [hrange, hpL0, hpL1] using hLMBi
    · simpa only [hrange] using hV
    · simpa only [hrange, hSC.frontier_eq_of_finrank_eq rfl] using hWCB
    · simpa only [hrange, hpC0, hpC1] using hWCBi
    · exact hwhole.frontier_eq_of_finrank_eq rfl

end PoincareConjecture.M76.Dehn
