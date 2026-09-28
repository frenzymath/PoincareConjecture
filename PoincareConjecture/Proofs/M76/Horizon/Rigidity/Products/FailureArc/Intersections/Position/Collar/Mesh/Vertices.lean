import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PointMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.FixedCollar
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_pair_chart_vertex_avoiding_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R U : Set X}
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (V : Finset X) (hU : IsOpen U) (hVU : (V : Set X) ⊆ U)
    (hcharts : ∀ p ∈ V, p ∈ S →
      ∃ (b : Bool) (C : OriginalSurfacePairChart e S T p b) (A : Set (ℝ × ℝ)),
        ∀ z ∈ C.coordinates.source,
          C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ A) :
    ∃ (F : X ≃ₜ X) (K : Set X),
      IsCompact K ∧ K ⊆ U ∧ EqOn F id Kᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F ⁻¹' T = T ∧ F ⁻¹' R = R ∧ Disjoint (F '' S) (V : Set X) := by
  classical
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he i j
  induction V using Finset.induction_on generalizing U with
  | empty =>
    exact ⟨Homeomorph.refl X, ∅, isCompact_empty, empty_subset _,
      fun _ _ => rfl, hid, hid, rfl, rfl, by simp⟩
  | @insert p V hpV ih =>
    let W := U ∩ ({p} : Set X)ᶜ
    have hW : IsOpen W := hU.inter isClosed_singleton.isOpen_compl
    have hVW : (V : Set X) ⊆ W := by
      intro x hx
      refine ⟨hVU (Finset.mem_insert_of_mem hx), ?_⟩
      intro hxp
      exact hpV ((mem_singleton_iff.mp hxp) ▸ hx)
    obtain ⟨F, K, hK, hKW, hFoff, hFPL, hFinv, hFT, hFR, hFV⟩ :=
      ih hW hVW (fun x hx => hcharts x (Finset.mem_insert_of_mem hx))
    have hpK : p ∉ K := fun hx => (hKW hx).2 (mem_singleton p)
    have hFp : F p = p := hFoff hpK
    by_cases hpS : p ∈ F '' S
    · have hpold : p ∈ S := by
        obtain ⟨x, hx, hxp⟩ := hpS
        exact F.injective (hxp.trans hFp.symm) ▸ hx
      obtain ⟨b, C, A, hA⟩ := hcharts p (Finset.mem_insert_self _ _) hpold
      let D := C.image_first_of_fixed_neighborhood F hK.isClosed.isOpen_compl hpK hFoff
      have hDA : ∀ z ∈ D.coordinates.source,
          D.chart.symm z ∈ R ↔ (D.coordinates z).1 ∈ A := by
        intro z hz
        exact hA z hz.1
      let O := U ∩ (V : Set X)ᶜ
      have hO : IsOpen O := hU.inter V.finite_toSet.isClosed.isOpen_compl
      have hpO : p ∈ O := ⟨hVU (Finset.mem_insert_self _ _), hpV⟩
      obtain ⟨G, L, hL, hLO, hGoff, hGPL, hGinv, hGT, hpG, hGmarks⟩ :=
        D.exists_target_preserving_point_motion he hO hpO
      have hGR := hGmarks R A hDA
      have hGfix (x : X) (hx : x ∈ (V : Set X)) : G x = x :=
        hGoff (fun h => (hLO h).2 hx)
      refine ⟨F.trans G, K ∪ L, hK.union hL,
        union_subset (hKW.trans inter_subset_left) (hLO.trans inter_subset_left), ?_,
        original_PL_motion_trans e hcover F G hFPL hGPL,
        original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv, ?_, ?_, ?_⟩
      · intro x hx
        change G (F x) = x
        rw [hFoff (fun h => hx (Or.inl h))]
        exact hGoff (fun h => hx (Or.inr h))
      · change F ⁻¹' (G ⁻¹' T) = T
        rw [hGT, hFT]
      · change F ⁻¹' (G ⁻¹' R) = R
        rw [hGR, hFR]
      · apply disjoint_left.mpr
        intro x hx hxV
        rcases Finset.mem_insert.mp hxV with hxp | hxV
        · apply hpG
          obtain ⟨y, hy, hyx⟩ := hx
          exact ⟨F y, ⟨y, hy, rfl⟩, hyx.trans hxp⟩
        · obtain ⟨y, hy, hyx⟩ := hx
          have hFy : F y = x := G.injective (hyx.trans (hGfix x hxV).symm)
          exact disjoint_left.mp hFV ⟨y, hy, hFy⟩ hxV
    · refine ⟨F, K, hK, hKW.trans inter_subset_left, hFoff, hFPL, hFinv,
        hFT, hFR, disjoint_left.mpr ?_⟩
      intro x hx hxV
      rcases Finset.mem_insert.mp hxV with hxp | hxV
      · exact hpS (hxp ▸ hx)
      · exact disjoint_left.mp hFV hx hxV

end PoincareConjecture.M76
