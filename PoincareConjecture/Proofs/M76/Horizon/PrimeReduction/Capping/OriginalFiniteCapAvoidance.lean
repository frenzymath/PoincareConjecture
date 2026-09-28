import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalChartCapAvoidance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCapNeighborhood
import Mathlib.Order.Filter.Bases.Finite

set_option autoImplicit false
open Set Geometry Topology
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_motion_avoiding_ball
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S D B R U : Set X}
    (s : ChartwisePLSphere e S) (b : ChartwisePLBall e D B)
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ interior R)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∩ interior R ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (F '' S)) ∧ Disjoint (F '' S) D := by
  obtain ⟨Q,hDQ,hQU,hQT,hQ⟩ := b.exists_enclosing_chart_in_domain hR he hDR hU hDU
  obtain ⟨F,C,hC,hCQ,hfix,hPL,hinv,sF,hdis⟩ :=
    s.exists_motion_avoiding_compact_in_ball_chart b.isCompact he.cover he.compatible Q hQT hQ hDQ
  exact ⟨F,C,hC,hCQ.trans hQU,hfix,hPL,hinv,sF,hdis⟩

theorem ChartwisePLSphere.exists_motion_avoiding_finite_balls
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {S R U : Set X}
    (s : ChartwisePLSphere e S) (D B : κ → Set X)
    (b : ∀ j, ChartwisePLBall e (D j) (B j))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hR : IsCompact R) (he : PLDomain e R) (hDR : ∀ j, D j ⊆ interior R)
    (hU : IsOpen U) (hDU : ∀ j, D j ⊆ U) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∩ interior R ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (F '' S)) ∧ Disjoint (F '' S) (⋃ j,D j) := by
  classical
  letI := Fintype.ofFinite κ
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (D i)) (𝓝ˢ (D j))) := by
    intro i j hij
    exact (SeparatedNhds.of_isCompact_isCompact (b i).isCompact
      (b j).isCompact (hdis hij)).disjoint_nhdsSet
  obtain ⟨O,hO,hOD⟩ := hd.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (D i))
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈ piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he.compatible i j
  have hfinite (T : Finset κ) :
      ∃ (F : X ≃ₜ X) (C : Set X),
        IsCompact C ∧ C ⊆ U ∩ interior R ∧ EqOn F id Cᶜ ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        Nonempty (ChartwisePLSphere e (F '' S)) ∧
        ∀ j ∈ T, Disjoint (F '' S) (D j) := by
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨Homeomorph.refl X,∅,isCompact_empty,empty_subset _,by intro x _; rfl,
        hid,hid,s.nonempty_image (Homeomorph.refl X) he.cover hid,by simp⟩
    | @insert j T hj ih =>
      obtain ⟨F,C,hC,hCU,hFfix,hFPL,hFinv,⟨sF⟩,hclear⟩ := ih
      obtain ⟨G,A,hA,hAO,hGfix,hGPL,hGinv,_,hnew⟩ :=
        sF.exists_motion_avoiding_ball (b j) hR he (hDR j) ((hO j).1.inter hU)
          (subset_inter (hO j).2 (hDU j))
      have hPL := original_PL_motion_trans e he.cover F G hFPL hGPL
      refine ⟨F.trans G,C ∪ A,hC.union hA,union_subset hCU
        (fun _ hx => ⟨(hAO hx).1.2,(hAO hx).2⟩),?_,hPL,
        original_PL_motion_trans e he.cover G.symm F.symm hGinv hFinv,
        s.nonempty_image (F.trans G) he.cover hPL,?_⟩
      · intro x hx
        change G (F x) = x
        rw [hFfix (fun h => hx (Or.inl h))]
        exact hGfix (fun h => hx (Or.inr h))
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · rw [image_image] at hnew
          exact hnew
        · have hjk : j ≠ k := fun h => hj (h.symm ▸ hk)
          apply disjoint_left.mpr
          rintro y ⟨x,hx,hxy⟩ hy
          have hGy : G y = y := hGfix (fun hyA =>
            disjoint_left.mp (hOD hjk) (hAO hyA).1.1 ((hO k).2 hy))
          have hFy : F x = y := G.injective (hxy.trans hGy.symm)
          exact disjoint_left.mp (hclear k hk) ⟨x,hx,hFy⟩ hy
  obtain ⟨F,C,hC,hCU,hfix,hPL,hinv,sF,hclear⟩ := hfinite Finset.univ
  exact ⟨F,C,hC,hCU,hfix,hPL,hinv,sF,
    disjoint_iUnion_right.mpr (fun j => hclear j (Finset.mem_univ j))⟩

end PoincareConjecture.M76
