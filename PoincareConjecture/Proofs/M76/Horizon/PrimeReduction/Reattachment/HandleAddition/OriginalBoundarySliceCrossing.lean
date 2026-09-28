import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.RegularBoundaryHeightChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalProductHeightExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorSurfaceGerms
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Frontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.RetainedCharts

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_regular_boundary_pair_charts_of_local_height
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R T : Set X}
    (S : ℝ → Set X) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃L[ℝ] C3) {f : C3 → ℝ} {U : Set C3}
    (hf : LocallyPiecewiseAffineOn f U) (hU : U ⊆ L '' Q.target)
    (hR : ∀ z ∈ U,Q.symm (L.symm z) ∈ R ↔ 0 ≤ z.1.2)
    (hT : ∀ z ∈ U,Q.symm (L.symm z) ∈ T ↔ z.1.1 = 0 ∧ 0 ≤ z.1.2)
    (hS : ∀ t,∀ z ∈ U,Q.symm (L.symm z) ∈ S t ↔ f z = t ∧ 0 ≤ z.1.2)
    {x : C3} (hx : x ∈ U) :
    ∃ (V : Set C3) (W : Set ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ W.Finite ∧
      ∀ y ∈ Q.source,L (Q y) ∈ V → (L (Q y)).1 = 0 → f (L (Q y)) ∉ W →
        ∃ C : OriginalSurfacePairChart e (S (f (L (Q y)))) T y true,
          (∀ z ∈ C.coordinates.source,C.chart.symm z ∈ R ↔
            0 ≤ (C.coordinates z).1.2) ∧
          ∀ z ∈ C.coordinates.source,C.chart.symm z ∈ frontier R ↔
            (C.coordinates z).1.2 = 0 := by
  obtain ⟨V,W,hV,hxV,hVU,hW,hcharts⟩ :=
    SimplicialComplex.exists_regular_height_charts_preserving_two_planes hf hx
  refine ⟨V,W,hV,hxV,hVU,hW,?_⟩
  intro y hyQ hyV hyzero hyW
  obtain ⟨H,hyH,hHy,hHV,hH,hfirst,hheight⟩ := hcharts (L (Q y)) hyV hyzero hyW
  let A := L.toHomeomorph.toOpenPartialHomeomorph.trans H
  have hAs : A.source = L ⁻¹' H.source := by
    change univ ∩ L ⁻¹' H.source = L ⁻¹' H.source
    exact univ_inter _
  have hAU (z : V3) (hz : z ∈ A.source) : L z ∈ U :=
    hVU (hHV (hAs.subset hz))
  have hAtarget : A.source ⊆ Q.target := by
    intro z hz
    obtain ⟨w,hw,heq⟩ := hU (hAU z hz)
    exact L.injective heq ▸ hw
  have hAfirst (z : V3) (hz : z ∈ A.source) : (A z).1 = (L z).1 :=
    hfirst (L z) (hAs.subset hz)
  have hAheight (z : V3) (hz : z ∈ A.source) :
      (A z).2 = f (L z)-f (L (Q y)) := hheight (L z) (hAs.subset hz)
  have hAf : LocallyPiecewiseAffineOn A A.source := by
    exact hH.1.comp (locallyPiecewiseAffineOn_affine
      L.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ)
  have hAi : LocallyPiecewiseAffineOn A.symm A.target := by
    exact (locallyPiecewiseAffineOn_affine
      L.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ).comp hH.2
  let C : OriginalSurfacePairChart e (S (f (L (Q y)))) T y true := {
    chart := Q
    coordinates := A
    compatible := hQ
    center_source := hyQ
    center_coordinates := hAs.symm.subset hyH
    center_zero := hHy
    source_subset := hAtarget
    forwardPL := hAf
    inversePL := hAi
    first_surface := by
      intro z hz
      have hh := hS (f (L (Q y))) (L z) (hAU z hz)
      simpa only [L.symm_apply_apply,hAheight z hz,hAfirst z hz,sub_eq_zero,
        true_implies] using hh
    second_surface := by
      intro z hz
      have hh := hT (L z) (hAU z hz)
      simpa only [L.symm_apply_apply,hAfirst z hz,true_implies] using hh }
  have hCR : ∀ z ∈ C.coordinates.source,C.chart.symm z ∈ R ↔
      0 ≤ (C.coordinates z).1.2 := by
    intro z hz
    change Q.symm z ∈ R ↔ 0 ≤ (A z).1.2
    have hh := hR (L z) (hAU z hz)
    simpa only [L.symm_apply_apply,hAfirst z hz] using hh
  exact ⟨C,hCR,C.frontier_iff_of_region_halfspace hCR⟩

theorem OriginalDiskProduct.exists_local_regular_boundary_pair_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (L : V3 ≃L[ℝ] C3)
    (hR : ∀ x ∈ Q.source,x ∈ R ↔ 0 ≤ (L (Q x)).1.2)
    (hS : ∀ x ∈ Q.source,x ∈ S ↔ (L (Q x)).1.1 = 0)
    (hfront : ∀ x ∈ Q.source,x ∈ frontier R ↔ (L (Q x)).1.2 = 0)
    {z : (Fin 2 → ℝ) × ℝ}
    (hz : z ∈ closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1)
    (hzQ : P.map z ∈ Q.source) :
    ∃ (O : Set X) (W : Set ℝ),IsOpen O ∧ P.map z ∈ O ∧ W.Finite ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,∀ y ∈ O, y ∈ S ∩ frontier R →
        y ∈ (fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1 → t ∉ W →
        ∃ C : OriginalSurfacePairChart e
          ((fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1) (S ∩ R) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔
            0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
            (C.coordinates v).1.2 = 0 := by
  obtain ⟨f,U,O,hU,hf,hO,hzO,hOQ,hQU,hlevels,hvalues⟩ :=
    P.exists_local_height_extension hopen Q hQ hz hzQ
  let V := L '' (Q '' O)
  have hQV : IsOpen (Q '' O) := Q.isOpen_image_of_subset_source hO hOQ
  have hV : IsOpen V := L.toHomeomorph.isOpenMap _ hQV
  have hVp (w : C3) (hw : w ∈ V) : Q.symm (L.symm w) ∈ O := by
    obtain ⟨_,⟨a,ha,rfl⟩,rfl⟩ := hw
    simpa only [L.symm_apply_apply,Q.left_inv (hOQ ha)] using ha
  have hVL (w : C3) (hw : w ∈ V) : L.symm w ∈ Q.target := by
    obtain ⟨_,⟨a,ha,rfl⟩,rfl⟩ := hw
    simpa only [L.symm_apply_apply] using Q.mapsTo (hOQ ha)
  have hVU : V ⊆ L.symm ⁻¹' U := by
    rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
    simpa only [mem_preimage,L.symm_apply_apply] using hQU ⟨a,ha,rfl⟩
  have hfL : LocallyPiecewiseAffineOn (f ∘ L.symm) V := by
    have hh := hf.comp (locallyPiecewiseAffineOn_affine
      L.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ)
    exact hh.mono hV (fun w hw => ⟨mem_univ _,hVU hw⟩)
  let slices (t : ℝ) := (fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1
  have hlevels' (t : ℝ) (w : C3) (hw : w ∈ V) :
      Q.symm (L.symm w) ∈ (if t ∈ Icc (-1 : ℝ) 1 then slices t else
        {a | a ∈ R ∧ f (Q a) = t}) ↔
        (f ∘ L.symm) w = t ∧ 0 ≤ w.1.2 := by
    have hp := hR _ (hOQ (hVp w hw))
    rw [Q.right_inv (hVL w hw),L.apply_symm_apply] at hp
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [if_pos ht,hlevels t ht _ (hVp w hw),hp,Q.right_inv (hVL w hw),and_comm]
      rfl
    · rw [if_neg ht]
      change (Q.symm (L.symm w) ∈ R ∧ f (Q (Q.symm (L.symm w))) = t) ↔ _
      rw [hp,Q.right_inv (hVL w hw),and_comm]
      rfl
  obtain ⟨V',W,hV',hzV',hV'V,hW,hcharts⟩ :=
    exists_regular_boundary_pair_charts_of_local_height
      (T := S ∩ R)
      (fun t => if t ∈ Icc (-1 : ℝ) 1 then slices t else {a | a ∈ R ∧ f (Q a) = t})
      Q hQ L hfL (by rintro _ ⟨w,hw,rfl⟩; exact ⟨w,Q.image_source_eq_target ▸
        image_mono hOQ hw,rfl⟩)
      (by intro w hw; simpa only [Q.right_inv (hVL w hw),L.apply_symm_apply] using
        hR _ (hOQ (hVp w hw)))
      (by intro w hw; simpa only [mem_inter_iff,Q.right_inv (hVL w hw),L.apply_symm_apply] using
        and_congr (hS _ (hOQ (hVp w hw))) (hR _ (hOQ (hVp w hw))))
      hlevels' (show L (Q (P.map z)) ∈ V from ⟨_,⟨_,hzO,rfl⟩,rfl⟩)
  let N := Q.source ∩ Q ⁻¹' (L ⁻¹' V')
  have hN : IsOpen N := Q.isOpen_inter_preimage (hV'.preimage L.continuous)
  refine ⟨N,W,hN,⟨hzQ,hzV'⟩,hW,?_⟩
  intro t ht y hy hySF hyt htW
  have hyO : y ∈ O := by
    have hh := hVp (L (Q y)) (hV'V hy.2)
    simpa only [L.symm_apply_apply,Q.left_inv hy.1] using hh
  have hfy : (f ∘ L.symm) (L (Q y)) = t := by
    simpa only [Function.comp_apply,L.symm_apply_apply] using
      ((hlevels t ht y hyO).mp hyt).2
  have hyaxis : (L (Q y)).1 = 0 :=
    Prod.ext ((hS y hy.1).mp hySF.1) ((hfront y hy.1).mp hySF.2)
  have hh := hcharts y hy.1 hy.2 hyaxis (by simpa only [hfy] using htW)
  have hset : (if (f ∘ L.symm) (L (Q y)) ∈ Icc (-1 : ℝ) 1 then
      slices ((f ∘ L.symm) (L (Q y))) else
      {a | a ∈ R ∧ f (Q a) = (f ∘ L.symm) (L (Q y))}) = slices t := by
    rw [hfy,if_pos ht]
  exact Eq.mp (congrArg (fun A : Set X =>
    ∃ C : OriginalSurfacePairChart e A (S ∩ R) y true,
      (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔ 0 ≤ (C.coordinates v).1.2) ∧
      ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
        (C.coordinates v).1.2 = 0) hset) hh

theorem OriginalDiskProduct.exists_finite_boundary_slice_exceptional_values
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))))
    (hclosed : IsClosed S)
    (hboundary : ∀ x ∈ S ∩ frontier R,
      ∃ (Q : OpenPartialHomeomorph X V3) (L : V3 ≃L[ℝ] C3),
        x ∈ Q.source ∧ (∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source,y ∈ R ↔ 0 ≤ (L (Q y)).1.2) ∧
        (∀ y ∈ Q.source,y ∈ S ↔ (L (Q y)).1.1 = 0) ∧
        ∀ y ∈ Q.source,y ∈ frontier R ↔ (L (Q y)).1.2 = 0)
    {a : ℝ} (ha : a < 1) :
    ∃ W : Set ℝ,W.Finite ∧
      ∀ t ∈ Icc (-a) a,t ∉ W → ∀ y,
        y ∈ (fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1 →
        y ∈ S ∩ frontier R →
        ∃ C : OriginalSurfacePairChart e
          ((fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1) (S ∩ R) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔
            0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
            (C.coordinates v).1.2 = 0 := by
  classical
  let K := (P.map '' (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Icc (-a) a)) ∩
    (S ∩ frontier R)
  have hband : Icc (-a) a ⊆ Ioo (-1 : ℝ) 1 :=
    fun t ht => ⟨lt_of_lt_of_le (neg_lt_neg ha) ht.1,lt_of_le_of_lt ht.2 ha⟩
  have hK : IsCompact K :=
    ((isCompact_closedBall (0 : Fin 2 → ℝ) 1).prod isCompact_Icc).image_of_continuousOn
      (P.polyhedral.continuousOn.mono (prod_mono subset_rfl (hband.trans Ioo_subset_Icc_self)))
      |>.inter_right (hclosed.inter isClosed_frontier)
  have hchoose (x : K) : ∃ (O : Set X) (W : Set ℝ),
      IsOpen O ∧ (x : X) ∈ O ∧ W.Finite ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,∀ y ∈ O,y ∈ S ∩ frontier R →
        y ∈ (fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1 → t ∉ W →
        ∃ C : OriginalSurfacePairChart e
          ((fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1) (S ∩ R) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔
            0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
            (C.coordinates v).1.2 = 0 := by
    obtain ⟨Q,L,hxQ,hQ,hR,hS,hfront⟩ := hboundary x x.property.2
    obtain ⟨z,hz,hzx⟩ := x.property.1
    obtain ⟨O,W,hO,hzO,hW,hcharts⟩ := P.exists_local_regular_boundary_pair_charts
      hopen Q hQ L hR hS hfront ⟨hz.1,hband hz.2⟩ (by rwa [hzx])
    exact ⟨O,W,hO,hzx ▸ hzO,hW,hcharts⟩
  choose O W hO hxO hW hcharts using hchoose
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover O hO
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxO ⟨x,hx⟩⟩)
  refine ⟨⋃ x : s,W x.val,finite_iUnion (fun x => hW x.val),?_⟩
  intro t ht htW y hyt hyS
  have hyK : y ∈ K := by
    obtain ⟨u,hu,rfl⟩ := hyt
    exact ⟨⟨(u,t),⟨hu,ht⟩,rfl⟩,hyS⟩
  obtain ⟨x,hxs,hyO⟩ := mem_iUnion₂.mp (hs hyK)
  exact hcharts x t (Ioo_subset_Icc_self (hband ht)) y hyO hyS hyt
    (fun h => htW (mem_iUnion.mpr ⟨⟨x,hxs⟩,h⟩))

private noncomputable def boundarySliceCoordinates (positive : Bool) : V3 ≃L[ℝ] C3 :=
  let L : V3 ≃ₗ[ℝ] C3 := {
    toFun := fun x => ((x 1,if positive then x 0 else -x 0),x 2)
    invFun := fun z => ![if positive then z.1.2 else -z.1.2,z.1.1,z.2]
    left_inv := by intro x; cases positive <;> funext i <;> fin_cases i <;> simp
    right_inv := by intro z; cases positive <;> simp
    map_add' := by intro x y; cases positive <;> simp [add_comm]
    map_smul' := by intro r x; cases positive <;> simp }
  L.toContinuousLinearEquiv

theorem OriginalDiskProduct.exists_finite_boundary_slice_exceptional_values_of_signed_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))))
    (hclosed : IsClosed S)
    (hboundary : ∀ x ∈ S ∩ frontier R,∃ Q : OpenPartialHomeomorph X V3,
      x ∈ Q.source ∧ (∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source,y ∈ S ↔ Q y 1 = 0) ∧
      (∀ y ∈ Q.source,y ∈ frontier R ↔ Q y 0 = 0) ∧
      ((∀ y ∈ Q.source,y ∈ R ↔ 0 ≤ Q y 0) ∨
        (∀ y ∈ Q.source,y ∈ R ↔ Q y 0 ≤ 0)))
    {a : ℝ} (ha : a < 1) :
    ∃ W : Set ℝ,W.Finite ∧
      ∀ t ∈ Icc (-a) a,t ∉ W → ∀ y,
        y ∈ (fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1 →
        y ∈ S ∩ frontier R →
        ∃ C : OriginalSurfacePairChart e
          ((fun u : Fin 2 → ℝ => P.map (u,t)) '' closedBall 0 1) (S ∩ R) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔
            0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
            (C.coordinates v).1.2 = 0 := by
  apply P.exists_finite_boundary_slice_exceptional_values hopen hclosed _ ha
  intro x hx
  obtain ⟨Q,hxQ,hQ,hS,hfront,hpos | hneg⟩ := hboundary x hx
  · exact ⟨Q,boundarySliceCoordinates true,hxQ,hQ,hpos,hS,hfront⟩
  · refine ⟨Q,boundarySliceCoordinates false,hxQ,hQ,?_,hS,?_⟩
    · intro y hy
      change (y ∈ R ↔ 0 ≤ -Q y 0)
      simpa only [neg_nonneg] using hneg y hy
    · intro y hy
      change (y ∈ frontier R ↔ -Q y 0 = 0)
      simpa only [neg_eq_zero] using hfront y hy

theorem OriginalDiskProduct.exists_regular_boundary_crossing_heights
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))))
    (hboundary : ∀ x ∈ S ∩ frontier R,∃ Q : OpenPartialHomeomorph X V3,
      x ∈ Q.source ∧ Q x = 0 ∧
      (∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source,y ∈ S ↔ Q y 1 = 0) ∧
      ∀ y ∈ Q.source,y ∈ frontier R ↔ Q y 0 = 0) :
    ∃ W : Set ℝ,W.Finite ∧
      ∀ t ∈ Icc (-(1/2) : ℝ) (1/2),t ∉ W → ∀ y ∈ S ∩ frontier R,
        y ∈ P.slice t '' closedBall (0 : Fin 2 → ℝ) 1 →
        ∃ C : OriginalSurfacePairChart e (S ∩ R)
          (P.slice t '' closedBall (0 : Fin 2 → ℝ) 1) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔
            0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
            (C.coordinates v).1.2 = 0 := by
  have hsigned : ∀ x ∈ S ∩ frontier R,∃ Q : OpenPartialHomeomorph X V3,
      x ∈ Q.source ∧ (∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source,y ∈ S ↔ Q y 1 = 0) ∧
      (∀ y ∈ Q.source,y ∈ frontier R ↔ Q y 0 = 0) ∧
      ((∀ y ∈ Q.source,y ∈ R ↔ 0 ≤ Q y 0) ∨
        (∀ y ∈ Q.source,y ∈ R ↔ Q y 0 ≤ 0)) := by
    intro x hx
    obtain ⟨Q,hxQ,hQx,hQ,hS,hfront⟩ := hboundary x hx
    obtain ⟨T,hxT,_,hT,hTS,hTF,hTR⟩ :=
      exists_signed_frontier_crossing_chart he hx.2 Q hxQ hQx hQ hS hfront
    exact ⟨T,hxT,hT,hTS,hTF,hTR⟩
  obtain ⟨W,hW,hcharts⟩ := P.exists_finite_boundary_slice_exceptional_values_of_signed_charts
    hopen s.isCompact.isClosed hsigned (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨W,hW,?_⟩
  intro t ht htW y hy hyt
  obtain ⟨C,hCR,hCF⟩ := hcharts t ht htW y hyt hy
  exact C.swap_boundary_region hCR hCF

theorem OriginalDiskProduct.exists_regular_boundary_crossing_heights_in_contact_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (closedBall (0 : Fin 2 → ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1))))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hSQ : S ∩ frontier R ⊆ Q.source)
    (hcross : ∀ w ∈ Q '' (S ∩ frontier R),
      ∃ C : OpenPartialHomeomorph V3 C3,w ∈ C.source ∧ C w = 0 ∧
        LocallyPiecewiseAffineOn C C.source ∧
        (∀ z ∈ C.source,Q.symm z ∈ S ↔ (C z).2 = 0) ∧
        ∀ z ∈ C.source,Q.symm z ∈ frontier R ↔ (C z).1.1 = 0) :
    ∃ W : Set ℝ,W.Finite ∧
      ∀ t ∈ Icc (-(1/2) : ℝ) (1/2),t ∉ W → ∀ y ∈ S ∩ frontier R,
        y ∈ P.slice t '' closedBall (0 : Fin 2 → ℝ) 1 →
        ∃ C : OriginalSurfacePairChart e (S ∩ R)
          (P.slice t '' closedBall (0 : Fin 2 → ℝ) 1) y true,
          (∀ v ∈ C.coordinates.source,C.chart.symm v ∈ R ↔
            0 ≤ (C.coordinates v).1.2) ∧
          ∀ v ∈ C.coordinates.source,C.chart.symm v ∈ frontier R ↔
            (C.coordinates v).1.2 = 0 := by
  apply P.exists_regular_boundary_crossing_heights s he hopen
  intro x hx
  obtain ⟨C,hxC,hCx,hC,hS,hfront⟩ := hcross (Q x) ⟨x,hx,rfl⟩
  exact compatible_paired_chart_of_coordinate_crossing Q hQ C hC
    (hSQ hx) hxC hCx hS hfront

end PoincareConjecture.M76
