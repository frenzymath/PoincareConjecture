import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedUpperResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedAlternateResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndUniqueness

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "i0" => (0 : unitInterval)
local notation "i1" => (1 : unitInterval)

theorem exists_normalized_resolution_pair
    {EA EM EC F X ι : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {SA QA WA : Set EA} {SM QM LM RM : Set EM} {SC QC WC : Set EC}
    {aA bA : EA} {aL bL aR bR : EM} {aC bC : EC}
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
    (hpA0 : (pA i0 : EA) = aA) (hpA1 : (pA i1 : EA) = bA)
    (hpL0 : (pL i0 : EM) = aL) (hpL1 : (pL i1 : EM) = bL)
    (hpR0 : (pR i0 : EM) = aR) (hpR1 : (pR i1 : EM) = bR)
    (hpC0 : (pC i0 : EC) = aC) (hpC1 : (pC i1 : EC) = bC)
    {fA : EA → X} {fM : EM → X} {fC : EC → X} {τ : C3 → X}
    (hfA : PolyhedralPLInCharts e fA SA) (hfM : PolyhedralPLInCharts e fM SM)
    (hfC : PolyhedralPLInCharts e fC SC) (hτ : PolyhedralPLInCharts e τ tube)
    (hA : ∀ t : I01, fA (pA t) = τ (((-1, 1), (t : ℝ)) : C3))
    (hL : ∀ t : I01, fM (pL t) = τ (((-1, -1), (t : ℝ)) : C3))
    (hR : ∀ t : I01, fM (pR t) = τ (((1, -1), (t : ℝ)) : C3))
    (hC : ∀ t : I01, fC (pC t) = τ (((1, 1), (t : ℝ)) : C3))
    (Z : Set X) (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (hQA : QA = (SA ∩ fA ⁻¹' Z) ∪ WA)
    (hQM : QM = ((SM ∩ fM ⁻¹' Z) ∪ RM) ∪ LM)
    (hQC : QC = (SC ∩ fC ⁻¹' Z) ∪ WC)
    (hmarkA : WA ∩ fA ⁻¹' Z = {aA, bA})
    (hmarkL : LM ∩ fM ⁻¹' Z = {aL, bL})
    (hmarkR : RM ∩ fM ⁻¹' Z = {aR, bR})
    (hmarkC : WC ∩ fC ⁻¹' Z = {aC, bC}) :
    ∃ (d0 : MarkedResolutionEndData Z τ (1 / 4) 0)
      (d1 : MarkedResolutionEndData Z τ (1 / 4) 1)
      (J K : Set EM) (qA : I01 ≃ₜ (SA ∩ fA ⁻¹' Z : Set EA))
      (qC : I01 ≃ₜ (SC ∩ fC ⁻¹' Z : Set EC)) (qD : I01 ≃ₜ J) (qB : I01 ≃ₜ K)
      (a : Path d0.a d1.a) (c : Path d1.c d0.c)
      (gU gV : V2 → X) (RU RV : Path d0.c d0.c),
      Nonempty (UpperResolutionSources SA SC source
        (fun t ↦ pA t) (fun t ↦ pC t)
        (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
        (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
        fA (τ ∘ strip (1 / 4) true) fC gU) ∧
      Nonempty (AlternateResolutionSources SA SM SC source
        (fun t ↦ pA t) (fun t ↦ pL t) (fun t ↦ pR t) (fun t ↦ pC t)
        (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
        (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
        fA (τ ∘ alternate (1 / 4) false) fM (τ ∘ alternate (1 / 4) true) fC gV) ∧
      qA.IsFinitePL ∧ qC.IsFinitePL ∧ qD.IsFinitePL ∧ qB.IsFinitePL ∧
      (qA i0 : EA) = aA ∧ (qA i1 : EA) = bA ∧
      (qC i0 : EC) = aC ∧ (qC i1 : EC) = bC ∧
      (qD i0 : EM) = aL ∧ (qB i1 : EM) = bL ∧
      Disjoint J K ∧ J ∪ K = SM ∩ fM ⁻¹' Z ∧
      (∀ t : I01, (a t : X) = fA (qA t)) ∧
      (∀ t : I01, (c.symm t : X) = fC (qC t)) ∧
      PolyhedralPLInCharts e gU D ∧ PolyhedralPLInCharts e gV D ∧
      gU '' D = (fA '' SA ∪ τ '' (strip (1 / 4) true '' source)) ∪ fC '' SC ∧
      gV '' D = (((fA '' SA ∪ τ '' (alternate (1 / 4) false '' source)) ∪
        fM '' SM) ∪ τ '' (alternate (1 / 4) true '' source)) ∪ fC '' SC ∧
      (∀ x ∈ D, gU x ∈ Z ↔ x ∈ Q) ∧ (∀ x ∈ D, gV x ∈ Z ↔ x ∈ Q) ∧
      (∀ t : I01, (RU t : X) = gU (squareRimLoop t)) ∧
      (∀ t : I01, (RV t : X) = gV (squareRimLoop t)) ∧
      RU.Homotopic (((d0.U.symm.trans a).trans d1.U).trans c) ∧
      ((∃ (d : Path d0.l d0.r) (β : Path d1.r d1.l),
        (qD i1 : EM) = aR ∧ (qB i0 : EM) = bR ∧
        (∀ t : I01, (d t : X) = fM (qD t)) ∧
        (∀ t : I01, (β t : X) = fM (qB t)) ∧
        RV.Homotopic (((((((d0.R.symm.trans d.symm).trans d0.L).trans a).trans
          d1.L.symm).trans β.symm).trans d1.R).trans c)) ∨
      (∃ (d : Path d0.l d1.r) (β : Path d0.r d1.l),
        (qD i1 : EM) = bR ∧ (qB i0 : EM) = aR ∧
        (∀ t : I01, (d t : X) = fM (qD t)) ∧
        (∀ t : I01, (β t : X) = fM (qB t)) ∧
        RV.Homotopic (((((((d0.R.symm.trans β).trans d1.L).trans a.symm).trans
          d0.L.symm).trans d).trans d1.R).trans c))) := by
  obtain ⟨d0, d1, J, K, qA, qC, qD, qB, a, c, gV, RV, sourcesV,
      hqA, hqC, hqD, hqB, hqA0, hqA1, hqC0, hqC1, hqD0, hqB1,
      hJK, hJKcover, haval, hcval, hgV, himV, hproperV, hRV, hcases⟩ :=
    exists_normalized_alternate_resolution_disk_map_with_sources
      e hcompat hSA hSM hSC hWA hLM hRM hWC
      hWAQ hLMQ hRMQ hWCQ hdisj habA habL habC pA pL pR pC hpA hpL hpR hpC
      hpA0 hpA1 hpL0 hpL1 hpR0 hpR1 hpC0 hpC1 hfA hfM hfC hτ hA hL hR hC
      Z hτZ hQA hQM hQC hmarkA hmarkL hmarkR hmarkC
  obtain ⟨u0, u1, qAU, qCU, aU, cU, gU, RU, sourcesU,
      _, _, hqAU0, hqAU1, hqCU0, hqCU1, haUval, hcUval,
      hgU, himU, hproperU, hRU, hRUhom⟩ :=
    exists_normalized_upper_resolution_disk_map_with_sources e hcompat hSA hSC hWA hWC
      hWAQ hWCQ habA habC pA pC hpA hpC hpA0 hpA1 hpC0 hpC1
      hfA hfC hτ hA hC Z hτZ hQA hQC hmarkA hmarkC
  have hu0 : u0 = d0 := u0.eq d0
  have hu1 : u1 = d1 := u1.eq d1
  subst u0 u1
  have ha : aU.Homotopic a := marked_interval_chart_paths_homotopic
    qAU qA hqAU0 hqAU1 hqA0 hqA1 fA (hfA.continuousOn.mono inter_subset_left)
    (fun _ hx ↦ hx.2) aU a haUval haval
  have hc : cU.Homotopic c := by
    have h := marked_interval_chart_paths_homotopic
      qCU qC hqCU0 hqCU1 hqC0 hqC1 fC (hfC.continuousOn.mono inter_subset_left)
      (fun _ hx ↦ hx.2) cU.symm c.symm hcUval hcval
    simpa only [Path.symm_symm] using h.symm₂
  have hhom := (((Path.Homotopic.refl d0.U.symm).hcomp ha).hcomp
    (Path.Homotopic.refl d1.U)).hcomp hc
  exact ⟨d0, d1, J, K, qA, qC, qD, qB, a, c, gU, gV, RU, RV, sourcesU, sourcesV,
    hqA, hqC, hqD, hqB, hqA0, hqA1, hqC0, hqC1, hqD0, hqB1,
    hJK, hJKcover, haval, hcval, hgU, hgV, himU, himV, hproperU, hproperV,
    hRU, hRV, hRUhom.trans hhom, hcases⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
