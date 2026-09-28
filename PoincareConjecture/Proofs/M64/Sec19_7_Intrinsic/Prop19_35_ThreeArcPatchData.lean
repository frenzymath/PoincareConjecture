import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedPatchData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcJoinPatch





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_exists_three_arc_patch_data
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S speed : ℝ} (hg : ∀ e, ContDiff ℝ ∞ (gamma e))
    (hs : Continuous sigma) (hT : ∀ e, 0 < T e) (hS : 0 < S) (hspeed : 0 < speed)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e)))
    (hjoin : gamma false (T false) = gamma true 0)
    (hreg : deriv (gamma false) (T false) ≠ 0)
    (htan : deriv (gamma true) 0 = speed • deriv (gamma false) (T false))
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hregular : ∀ t ∈ Ioo (0 : ℝ) (T false), deriv (gamma false) t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) (T false), ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma false t + z • quarterTurn (deriv (gamma false) t) ∈ U)
    (C : M64IntrinsicThreeArcCaps gamma sigma T S U) :
    ∃ b : Bool → ℝ, (∀ e, b e ∈ Ioo (0 : ℝ) (T e)) ∧
      (∀ e : Bool, (if e then b e else C.radius e) <
        if e then T e - C.radius e else b e) ∧
      ∃ P : M64IntrinsicJoinedBandPatch gamma T b U,
        P.direction = quarterTurn (deriv (gamma false) (T false)) ∧
        ∀ e, (P.band e).carrier ⊆
          (C.carrier false ∪ C.carrier true ∪ sigma '' Icc 0 S)ᶜ := by
  classical
  obtain ⟨_, _, epsilon, hepsilon, hgap0, hgap1, hb0, hb1,
      L, R, f, g, a0, a1, c0, c1, ha, hc, hbase0, hjoin0, hjoin1, hbase1,
      htrans0, htrans1, htan0, htan1, cutoff, hcutoff, hbands⟩ :=
    m64Intrinsic_exists_three_arc_join_patch (hg false) (hg true) hs
      (hT false) (hT true) hS hspeed (C.radius_bound false) (C.radius_bound true)
      (hinj false) (hinj true) hjoin hreg htan hab has hbs hregular
      hU hV hUV hfront hfV hray (C.compact false) (C.compact true)
      (C.frontier_contact false).subset (C.frontier_contact true).subset
  let rho := cutoff / 2
  have hrho : rho ∈ Ioo (0 : ℝ) cutoff := ⟨half_pos hcutoff, half_lt_self hcutoff⟩
  obtain ⟨B0, B1, hlower0, hlower1, hO0, hO1, hsub0, hsub1, hopen0, hopen1,
      _, _, _, _, hinter, _⟩ := hbands rho hrho rho hrho rho hrho
  let b : Bool → ℝ := fun e => if e then epsilon else T false - epsilon
  let frame : Bool → (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates := fun e => if e then R else L
  let graph : Bool → ℝ → ℝ := fun e => if e then g else f
  let left : Bool → ℝ := fun e => if e then c0 else a0
  let right : Bool → ℝ := fun e => if e then c1 else a1
  let P : M64IntrinsicJoinedBandPatch gamma T b U :=
    { frame := frame
      graph := graph
      left := left
      right := right
      increasing := by
        intro e
        cases e
        · exact ha
        · exact hc
      direction := quarterTurn (deriv (gamma false) (T false))
      left_length := rho
      middle_length := rho
      right_length := rho
      band := fun e => Bool.rec B0 B1 e
      left_base := by
        intro e
        cases e
        · exact hbase0
        · exact hjoin1
      right_base := by
        intro e
        cases e
        · exact hjoin0
        · exact hbase1
      transverse := by
        intro e
        cases e
        · exact htrans0
        · exact htrans1
      tangent := by
        intro e
        cases e
        · exact htan0
        · exact htan1
      lower_arc := by
        intro e
        cases e
        · exact hlower0
        · exact hlower1
      occupied := by
        intro e
        cases e
        · exact hsub0
        · exact hsub1
      off_lower := by
        intro e
        cases e
        · exact hopen0
        · exact hopen1
      intersection := hinter }
  refine ⟨b, ?_, ?_, P, rfl, ?_⟩
  · intro e
    cases e
    · exact ⟨hb0, sub_lt_self _ hepsilon⟩
    · exact ⟨hepsilon, hb1⟩
  · intro e
    cases e
    · exact hgap0
    · exact hgap1
  · intro e
    cases e
    · exact hO0
    · exact hO1

end PoincareConjecture
