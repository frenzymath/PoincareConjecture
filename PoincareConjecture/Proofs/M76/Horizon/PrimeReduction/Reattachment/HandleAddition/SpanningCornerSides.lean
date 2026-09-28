import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ConvexFrontierSides
import PoincareConjecture.Proofs.M76.Mathlib.PlanarRegionSideTransport

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem signed_side_of_relative_corner_frontier
    {X : Type*} [TopologicalSpace X] {E W : Set X}
    (hW : IsClosed W) (hreg : closure (interior W) = W)
    (H : OpenPartialHomeomorph X C3) (hcv : Convex ℝ H.target)
    {x₀ : X} (hx₀ : x₀ ∈ H.source) (hzero : H x₀ = 0)
    (hE : ∀ x ∈ H.source,x ∈ E ↔ 0 ≤ (H x).1.2)
    (hfront : ∀ x ∈ H.source,x ∈ frontier W ∩ E ↔
      (H x).1.1 = 0 ∧ 0 ≤ (H x).1.2) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ x ∈ H.source,x ∈ E → (x ∈ W ↔ 0 ≤ ε * (H x).1.1) := by
  let ell : C3 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let height : C3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  have htarget0 : (0 : C3) ∈ H.target := hzero ▸ H.map_source hx₀
  obtain ⟨r,hr,hrH⟩ := Metric.isOpen_iff.mp H.open_target 0 htarget0
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδr : δ < r := half_lt_self hr
  have hq : ((0,δ),0) ∈ H.target := by
    apply hrH
    rw [mem_ball_zero_iff]
    simpa [Prod.norm_def,Real.norm_eq_abs,abs_of_pos hδ] using And.intro hr hδr
  have hqP : ((δ,δ),0) ∈ H.target := by
    apply hrH
    rw [mem_ball_zero_iff]
    simpa [Prod.norm_def,Real.norm_eq_abs,abs_of_pos hδ] using And.intro hδr hr
  have hqN : ((-δ,δ),0) ∈ H.target := by
    apply hrH
    rw [mem_ball_zero_iff]
    simpa [Prod.norm_def,Real.norm_eq_abs,abs_of_pos hδ] using And.intro hδr hr
  let T := (H.symm.restrOpen (height ⁻¹' Ioi 0)
    (isOpen_Ioi.preimage height.continuous)).symm
  have hTtarget : T.target = H.target ∩ height ⁻¹' Ioi 0 := rfl
  have hTsource (x : X) : x ∈ T.source ↔ x ∈ H.source ∧ 0 < (H x).1.2 := Iff.rfl
  have hTval (x : X) : T x = H x := rfl
  have hqS : H.symm ((0,δ),0) ∈ T.source := by
    rw [hTsource]
    exact ⟨H.map_target hq,by rw [H.right_inv hq]; exact hδ⟩
  have hqfront : H.symm ((0,δ),0) ∈ frontier W := by
    apply ((hfront _ (H.map_target hq)).mpr ?_).1
    rw [H.right_inv hq]
    exact ⟨rfl,hδ.le⟩
  have hTf : ∀ x ∈ T.source,x ∈ frontier W ↔ ell (T x) = 0 := by
    intro x hx
    have hx' := (hTsource x).mp hx
    have hxE := (hE x hx'.1).mpr hx'.2.le
    change x ∈ frontier W ↔ (H x).1.1 = 0
    exact ⟨fun hw => ((hfront x hx'.1).mp ⟨hw,hxE⟩).1,
      fun hz => ((hfront x hx'.1).mpr ⟨hz,hx'.2.le⟩).1⟩
  have hTcv : Convex ℝ T.target := by
    rw [hTtarget]
    exact hcv.inter ((convex_Ioi (0 : ℝ)).linear_preimage height.toLinearMap)
  let P := H.symm '' ((H.target ∩ height ⁻¹' Ici 0) ∩ ell ⁻¹' Ioi 0)
  let N := H.symm '' ((H.target ∩ height ⁻¹' Ici 0) ∩ ell ⁻¹' Iio 0)
  have hP : IsPreconnected P :=
    ((hcv.inter ((convex_Ici (0 : ℝ)).linear_preimage height.toLinearMap)).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage ell.toLinearMap)).isPreconnected.image H.symm
        (H.continuousOn_symm.mono (inter_subset_left.trans inter_subset_left))
  have hN : IsPreconnected N :=
    ((hcv.inter ((convex_Ici (0 : ℝ)).linear_preimage height.toLinearMap)).inter
      ((convex_Iio (0 : ℝ)).linear_preimage ell.toLinearMap)).isPreconnected.image H.symm
        (H.continuousOn_symm.mono (inter_subset_left.trans inter_subset_left))
  have hPavoid : Disjoint P (frontier W) := by
    apply disjoint_left.mpr
    rintro x ⟨z,⟨⟨hz,hy⟩,hpos⟩,rfl⟩ hxf
    have hxE : H.symm z ∈ E := (hE _ (H.map_target hz)).mpr (by rwa [H.right_inv hz])
    have hh := ((hfront _ (H.map_target hz)).mp ⟨hxf,hxE⟩).1
    rw [H.right_inv hz] at hh
    exact (ne_of_gt hpos) hh
  have hNavoid : Disjoint N (frontier W) := by
    apply disjoint_left.mpr
    rintro x ⟨z,⟨⟨hz,hy⟩,hneg⟩,rfl⟩ hxf
    have hxE : H.symm z ∈ E := (hE _ (H.map_target hz)).mpr (by rwa [H.right_inv hz])
    have hh := ((hfront _ (H.map_target hz)).mp ⟨hxf,hxE⟩).1
    rw [H.right_inv hz] at hh
    exact (ne_of_lt hneg) hh
  have hpP : H.symm ((δ,δ),0) ∈ P := ⟨((δ,δ),0),⟨⟨hqP,hδ.le⟩,hδ⟩,rfl⟩
  have hnN : H.symm ((-δ,δ),0) ∈ N := ⟨((-δ,δ),0),⟨⟨hqN,hδ.le⟩,neg_neg_of_pos hδ⟩,rfl⟩
  have hpT : H.symm ((δ,δ),0) ∈ T.source := by
    rw [hTsource]
    exact ⟨H.map_target hqP,by rw [H.right_inv hqP]; exact hδ⟩
  have hnT : H.symm ((-δ,δ),0) ∈ T.source := by
    rw [hTsource]
    exact ⟨H.map_target hqN,by rw [H.right_inv hqN]; exact hδ⟩
  have hmemP (x : X) (hx : x ∈ H.source) (hy : 0 ≤ (H x).1.2)
      (hpos : 0 < (H x).1.1) : x ∈ W ↔ H.symm ((δ,δ),0) ∈ W :=
    hP.mem_iff_of_disjoint_frontier hPavoid
      ⟨H x,⟨⟨H.map_source hx,hy⟩,hpos⟩,H.left_inv hx⟩ hpP
  have hmemN (x : X) (hx : x ∈ H.source) (hy : 0 ≤ (H x).1.2)
      (hneg : (H x).1.1 < 0) : x ∈ W ↔ H.symm ((-δ,δ),0) ∈ W :=
    hN.mem_iff_of_disjoint_frontier hNavoid
      ⟨H x,⟨⟨H.map_source hx,hy⟩,hneg⟩,H.left_inv hx⟩ hnN
  have hzeroW (x : X) (hx : x ∈ H.source) (hy : 0 ≤ (H x).1.2)
      (hz : (H x).1.1 = 0) : x ∈ W :=
    hW.frontier_subset (((hfront x hx).mpr ⟨hz,hy⟩).1)
  rcases halfspace_of_convex_linear_frontier_chart hW hreg hqfront T hqS ell hTcv hTf with hp | hn
  · have hpW : H.symm ((δ,δ),0) ∈ W := (hp _ hpT).mpr (by
      change 0 ≤ (H (H.symm ((δ,δ),0))).1.1
      rw [H.right_inv hqP]
      exact hδ.le)
    have hnW : H.symm ((-δ,δ),0) ∉ W := by
      intro hw
      have hh := (hp _ hnT).mp hw
      change 0 ≤ (H (H.symm ((-δ,δ),0))).1.1 at hh
      rw [H.right_inv hqN] at hh
      linarith
    refine ⟨1,Or.inl rfl,?_⟩
    intro x hx hxE
    have hy := (hE x hx).mp hxE
    simp only [one_mul]
    rcases lt_trichotomy (H x).1.1 0 with hn | hz | hp
    · exact ⟨fun hw => (hnW ((hmemN x hx hy hn).mp hw)).elim,fun h => (not_le_of_gt hn h).elim⟩
    · exact iff_of_true (hzeroW x hx hy hz) hz.symm.le
    · exact iff_of_true ((hmemP x hx hy hp).mpr hpW) hp.le
  · have hpW : H.symm ((δ,δ),0) ∉ W := by
      intro hw
      have hh := (hn _ hpT).mp hw
      change (H (H.symm ((δ,δ),0))).1.1 ≤ 0 at hh
      rw [H.right_inv hqP] at hh
      linarith
    have hnW : H.symm ((-δ,δ),0) ∈ W := (hn _ hnT).mpr (by
      change (H (H.symm ((-δ,δ),0))).1.1 ≤ 0
      rw [H.right_inv hqN]
      linarith)
    refine ⟨-1,Or.inr rfl,?_⟩
    intro x hx hxE
    have hy := (hE x hx).mp hxE
    simp only [neg_one_mul,neg_nonneg]
    rcases lt_trichotomy (H x).1.1 0 with hn | hz | hp
    · exact iff_of_true ((hmemN x hx hy hn).mpr hnW) hn.le
    · exact iff_of_true (hzeroW x hx hy hz) hz.le
    · exact ⟨fun hw => (hpW ((hmemP x hx hy hp).mp hw)).elim,fun h => (not_le_of_gt hp h).elim⟩

theorem frontier_corner_of_signed_relative_side
    {X : Type*} [TopologicalSpace X] {E W : Set X}
    (H : OpenPartialHomeomorph X C3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hE : ∀ x ∈ H.source,x ∈ E ↔ 0 ≤ (H x).1.2)
    (hW : ∀ x ∈ H.source,x ∈ E → (x ∈ W ↔ 0 ≤ ε * (H x).1.1)) :
    ∀ x ∈ H.source,x ∈ frontier (E ∩ W) ↔
      ((H x).1.2 = 0 ∧ 0 ≤ ε * (H x).1.1) ∨
        ((H x).1.1 = 0 ∧ 0 ≤ (H x).1.2) := by
  let Q : Set C3 := {z | 0 ≤ z.1.2 ∧ 0 ≤ ε * z.1.1}
  have hQ : H.IsImage (E ∩ W) Q := by
    intro x hx
    constructor
    · intro h
      have hxE := (hE x hx).mpr h.1
      exact ⟨hxE,(hW x hx hxE).mpr h.2⟩
    · intro h
      exact ⟨(hE x hx).mp h.1,(hW x hx h.1).mp h.2⟩
  have hQfront : ∀ z : C3,z ∈ frontier Q ↔
      (z.1.2 = 0 ∧ 0 ≤ ε * z.1.1) ∨ (z.1.1 = 0 ∧ 0 ≤ z.1.2) := by
    intro z
    rcases hε with rfl | rfl
    · have hq : Q = (Ici (0 : ℝ) ×ˢ Ici 0) ×ˢ (univ : Set ℝ) := by
        ext z
        simp only [Q,one_mul,mem_ofPred_eq,mem_prod,mem_Ici,mem_univ,and_true]
        exact and_comm
      rw [hq,frontier_prod_univ_eq,frontier_prod_eq]
      simp only [frontier_Ici,closure_Ici,mem_prod,mem_union,mem_singleton_iff,
        mem_Ici,mem_univ,and_true,one_mul]
      tauto
    · have hq : Q = (Iic (0 : ℝ) ×ˢ Ici 0) ×ˢ (univ : Set ℝ) := by
        ext z
        simp only [Q,neg_one_mul,neg_nonneg,mem_ofPred_eq,mem_prod,mem_Ici,mem_Iic,
          mem_univ,and_true]
        exact and_comm
      rw [hq,frontier_prod_univ_eq,frontier_prod_eq]
      simp only [frontier_Iic,closure_Iic,frontier_Ici,closure_Ici,mem_prod,mem_union,
        mem_singleton_iff,mem_Ici,mem_Iic,mem_univ,and_true,neg_one_mul,neg_nonneg]
      tauto
  intro x hx
  exact (hQ.frontier.apply_mem_iff hx).symm.trans (hQfront (H x))

theorem signed_corner_of_relative_frontier
    {X : Type*} [TopologicalSpace X] {E W : Set X}
    (hW : IsClosed W) (hreg : closure (interior W) = W)
    (H : OpenPartialHomeomorph X C3) (hcv : Convex ℝ H.target)
    {x₀ : X} (hx₀ : x₀ ∈ H.source) (hzero : H x₀ = 0)
    (hE : ∀ x ∈ H.source,x ∈ E ↔ 0 ≤ (H x).1.2)
    (hfront : ∀ x ∈ H.source,x ∈ frontier W ∩ E ↔
      (H x).1.1 = 0 ∧ 0 ≤ (H x).1.2) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ x ∈ H.source,x ∈ E → (x ∈ W ↔ 0 ≤ ε * (H x).1.1)) ∧
      ∀ x ∈ H.source,x ∈ frontier (E ∩ W) ↔
        ((H x).1.2 = 0 ∧ 0 ≤ ε * (H x).1.1) ∨
          ((H x).1.1 = 0 ∧ 0 ≤ (H x).1.2) := by
  obtain ⟨ε,hε,hside⟩ := signed_side_of_relative_corner_frontier hW hreg H hcv hx₀ hzero hE hfront
  exact ⟨ε,hε,hside,frontier_corner_of_signed_relative_side H hε hE hside⟩

end PoincareConjecture.M76
