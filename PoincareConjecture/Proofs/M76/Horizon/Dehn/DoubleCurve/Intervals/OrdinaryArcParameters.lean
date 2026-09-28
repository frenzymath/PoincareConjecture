import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OrdinaryModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}


theorem OrdinaryDoubleCurveModel.piece_subset_double
    (M : OrdinaryDoubleCurveModel e f R) (i : M.Index) :
    M.pieces i ⊆ doubleLocusOn f D2 := by
  rw [← M.cover]
  exact subset_iUnion _ i



theorem OrdinaryDoubleCurveModel.partner_component_iff
    (M : OrdinaryDoubleCurveModel e f R) (i : M.Index) (x : doubleLocusOn f D2) :
    (x : V2) ∈ M.pieces i ↔ (M.partner x : V2) ∈ M.pieces (M.mate i) := by
  constructor
  · exact M.partner_component i x
  · intro hx
    have h := M.partner_component (M.mate i) (M.partner x) hx
    simpa only [M.partner_involutive x, M.mate_involutive i] using h




theorem OrdinaryDoubleCurveModel.exists_interval_arc_parameters
    [T2Space X] (M : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (hinside : MapsTo f D2 R)
    (hfrontier : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : M.Index) (hball : IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ Q2)) :
    M.mate i ≠ i ∧
      ∃ (alpha : I01 ≃ₜ M.pieces i) (beta : I01 ≃ₜ M.pieces (M.mate i)) (arc : ℝ → X),
        alpha.IsFinitePL ∧ beta.IsFinitePL ∧
        (∀ u : I01, ∃ hx : (alpha u : V2) ∈ doubleLocusOn f D2,
          (beta u : V2) = (M.partner ⟨alpha u, hx⟩ : V2)) ∧
        M.pieces i ∩ Q2 = {(alpha 0 : V2), (alpha 1 : V2)} ∧
        M.pieces (M.mate i) ∩ Q2 = {(beta 0 : V2), (beta 1 : V2)} ∧
        IsEmbedding (fun u : I01 ↦ arc u) ∧ PolyhedralPLInCharts e arc (Icc (0 : ℝ) 1) ∧
        (∀ u : I01, arc u = f (alpha u) ∧ arc u = f (beta u)) ∧
        (∀ x ∈ D2, f x ∈ range (fun u : I01 ↦ arc u) ↔
          x ∈ M.pieces i ∪ M.pieces (M.mate i)) ∧
        (∀ u : I01, arc u ∈ frontier R ↔ u = 0 ∨ u = 1) ∧
        ∀ u : I01, u ≠ 0 → u ≠ 1 → arc u ∈ interior R := by
  have hsub := M.piece_subset_double
  have hmem := M.partner_component_iff
  have htri : ∃ K : SimplicialComplex ℝ V2, K.faces.Finite ∧ K.space = M.pieces i := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
    exact ⟨K, hK, hKs⟩
  obtain ⟨a, b, hab, habound⟩ := hball.exists_boundary_eq_pair
  have hball' : IsFinitePLBallPair ℝ (M.pieces i) {a, b} := by
    simpa only [habound] using hball
  obtain ⟨alpha, halpha, halpha0, halpha1⟩ := hball'.exists_unitInterval_chart_with_endpoints hab
  let d := M.partner.restrictSubsets (hsub i) (hsub (M.mate i)) (hmem i)
  obtain ⟨K, hK, hKs⟩ := htri
  have hd : d.IsFinitePL := M.partnerPL.restrictSubsets
    (hsub i) (hsub (M.mate i)) (hmem i) K hK hKs
  have hne : M.mate i ≠ i := by
    intro heq
    have hm : ∀ x : doubleLocusOn f D2,
        (x : V2) ∈ M.pieces i ↔ (M.partner x : V2) ∈ M.pieces i := by
      intro x
      simpa only [heq] using hmem i x
    let d0 := M.partner.restrictSubsets (hsub i) (hsub i) hm
    have hd0 : d0.IsFinitePL := M.partnerPL.restrictSubsets (hsub i) (hsub i) hm K hK hKs
    let e0 := alpha.trans (d0.trans alpha.symm)
    obtain ⟨F, hF, hFval⟩ := halpha.trans (hd0.trans halpha.symm)
    have hFI : MapsTo F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro x hx
      rw [← hFval ⟨x, hx⟩]
      exact (e0 ⟨x, hx⟩).property
    obtain ⟨x, hx, hFx⟩ := exists_mem_Icc_isFixedPt_of_mapsTo
      hF.continuousOn zero_le_one hFI
    have he0 : e0 ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext ((hFval ⟨x, hx⟩).trans hFx)
    have hd0fix : d0 (alpha ⟨x, hx⟩) = alpha ⟨x, hx⟩ := by
      have h := congrArg alpha he0
      change alpha (alpha.symm (d0 (alpha ⟨x, hx⟩))) = alpha ⟨x, hx⟩ at h
      simpa only [alpha.apply_symm_apply] using h
    exact M.partner_free ⟨alpha ⟨x, hx⟩, hsub i (alpha ⟨x, hx⟩).property⟩
      (congrArg (fun y : M.pieces i ↦ (y : V2)) hd0fix)
  let beta := alpha.trans d
  have hbeta : beta.IsFinitePL := halpha.trans hd
  have hbetaval (u : I01) : (beta u : V2) =
      (M.partner ⟨alpha u, hsub i (alpha u).property⟩ : V2) := rfl
  have halpharim : M.pieces i ∩ Q2 = {(alpha 0 : V2), (alpha 1 : V2)} := by
    have h0 : (alpha (0 : I01) : V2) = a := halpha0
    have h1 : (alpha (1 : I01) : V2) = b := halpha1
    rw [h0, h1]
    exact habound
  have hbetarim : M.pieces (M.mate i) ∩ Q2 = {(beta 0 : V2), (beta 1 : V2)} := by
    ext x
    constructor
    · intro hx
      let y : M.pieces i := d.symm ⟨x, hx.1⟩
      have hdx : (d y : V2) = x := congrArg Subtype.val (d.apply_symm_apply ⟨x, hx.1⟩)
      have hyr : (y : V2) ∈ Q2 :=
        (M.partner_rim ⟨y, hsub i y.property⟩).mp (hdx.symm ▸ hx.2)
      rcases halpharim.subset ⟨y.property, hyr⟩ with h0 | h1
      · exact Or.inl (hdx.symm.trans (congrArg (fun z : M.pieces i ↦ (d z : V2))
          (Subtype.ext h0)))
      · exact Or.inr (hdx.symm.trans (congrArg (fun z : M.pieces i ↦ (d z : V2))
          (Subtype.ext h1)))
    · rintro (rfl | rfl)
      · exact ⟨(beta 0).property, (M.partner_rim ⟨alpha 0, hsub i (alpha 0).property⟩).mpr
          (halpharim.symm.subset (Or.inl rfl)).2⟩
      · exact ⟨(beta 1).property, (M.partner_rim ⟨alpha 1, hsub i (alpha 1).property⟩).mpr
          (halpharim.symm.subset (Or.inr rfl)).2⟩
  obtain ⟨l, hl, hlval⟩ := halpha
  have hlD : MapsTo l (Icc (0 : ℝ) 1) D2 := by
    intro u hu
    rw [← hlval ⟨u, hu⟩]
    exact (hsub i (alpha ⟨u, hu⟩).property).1
  let arc := f ∘ l
  have harc (u : I01) : arc u = f (alpha u) := congrArg f (hlval u).symm
  have hsync (u : I01) : arc u = f (beta u) :=
    (harc u).trans (M.partner_value ⟨alpha u, hsub i (alpha u).property⟩).symm
  have harcPL : PolyhedralPLInCharts e arc (Icc (0 : ℝ) 1) := by
    obtain ⟨J, hJ, hJs, hlaff⟩ := hl
    have h := hf.comp_finitePiecewiseAffineOn J hJ
      (show FinitePiecewiseAffineOn l J.space from ⟨J, hJ, rfl, hlaff⟩)
      (by simpa only [hJs] using hlD)
    simpa only [hJs] using h
  have harci : Function.Injective (fun u : I01 ↦ arc u) := by
    intro u v huv
    have huG := hsub i (alpha u).property
    have hvG := hsub i (alpha v).property
    by_cases heq : (alpha u : V2) = (alpha v : V2)
    · exact alpha.injective (Subtype.ext heq)
    · have hval : f (alpha u) = f (alpha v) := (harc u).symm.trans (huv.trans (harc v))
      have h := M.unique_partner ⟨alpha u, huG⟩ (alpha v) hvG.1 hval heq
      exact (disjoint_left.mp (M.disjoint hne)
        ((hmem i ⟨alpha u, huG⟩).mp (alpha u).property)
        (h ▸ (alpha v).property)).elim
  have harcEmbedding : IsEmbedding (fun u : I01 ↦ arc u) :=
    (harcPL.continuousOn.domRestrict.isClosedEmbedding harci).isEmbedding
  have hpreimage (x : V2) (hx : x ∈ D2) : f x ∈ range (fun u : I01 ↦ arc u) ↔
      x ∈ M.pieces i ∪ M.pieces (M.mate i) := by
    constructor
    · rintro ⟨u, hu⟩
      by_cases hxu : (alpha u : V2) = x
      · exact Or.inl (hxu ▸ (alpha u).property)
      · have hval : f (alpha u) = f x := (harc u).symm.trans hu
        have h := M.unique_partner ⟨alpha u, hsub i (alpha u).property⟩ x hx hval hxu
        exact Or.inr (h.symm ▸ (hmem i ⟨alpha u, hsub i (alpha u).property⟩).mp
          (alpha u).property)
    · rintro (hxA | hxB)
      · refine ⟨alpha.symm ⟨x, hxA⟩, ?_⟩
        change arc (alpha.symm ⟨x, hxA⟩) = f x
        rw [harc, alpha.apply_symm_apply]
      · refine ⟨beta.symm ⟨x, hxB⟩, ?_⟩
        change arc (beta.symm ⟨x, hxB⟩) = f x
        rw [hsync, beta.apply_symm_apply]
  have hproper (u : I01) : arc u ∈ frontier R ↔ u = 0 ∨ u = 1 := by
    rw [harc, hfrontier _ (hsub i (alpha u).property).1]
    constructor
    · intro hu
      rcases halpharim.subset ⟨(alpha u).property, hu⟩ with h0 | h1
      · exact Or.inl (alpha.injective (Subtype.ext h0))
      · exact Or.inr (alpha.injective (Subtype.ext h1))
    · rintro (rfl | rfl)
      · exact (halpharim.symm.subset (Or.inl rfl)).2
      · exact (halpharim.symm.subset (Or.inr rfl)).2
  refine ⟨hne, alpha, beta, arc, ⟨l, hl, hlval⟩, hbeta,
    fun u ↦ ⟨hsub i (alpha u).property, hbetaval u⟩, halpharim, hbetarim,
    harcEmbedding, harcPL, fun u ↦ ⟨harc u, hsync u⟩, hpreimage, hproper, ?_⟩
  intro u hu0 hu1
  have hin : arc u ∈ R := by
    rw [harc]
    exact hinside (hsub i (alpha u).property).1
  have hn : arc u ∉ frontier R := by
    rw [hproper]
    exact not_or.mpr ⟨hu0, hu1⟩
  exact (closure_sdiff_frontier R).subset ⟨subset_closure hin, hn⟩

end PoincareConjecture.M76.Dehn
