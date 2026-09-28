import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCapProductCoordinates

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => Metric.closedBall (0 : V2) 1
local notation "Band" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem RelativeFrontierDiskProduct.exists_confined_base_extension
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V3} {D W O K : Set X}
    {j : V2 → X} {s : Finset (D ∪ K : Set X)}
    (P : RelativeFrontierDiskProduct e D W O j K s)
    {A B : Set V} (hA : IsFinitePLBallPair P2 A B)
    {a : V → X} (ha : PolyhedralPLInCharts e a A) (hai : InjOn a A)
    (haS : MapsTo a A (frontier D ∩ W))
    {U : Set X} (hU : IsOpen U) (haU : a '' A ⊆ U) :
    ∃ (ε : ℝ) (v : V × ℝ → X),
      0 < ε ∧ ε ≤ P.delta ∧
      (∀ z,v z = P.inverse (P.product (P.graph (a z.1),ε*z.2))) ∧
      PolyhedralPLInCharts e v (A ×ˢ J) ∧ InjOn v (A ×ˢ J) ∧
      MapsTo v (A ×ˢ J) (D ∩ W ∩ (U ∩ P.agreement)) ∧
      (∀ z ∈ A,v (z,0) = a z) ∧
      (∀ z ∈ A ×ˢ J,v z ∈ frontier D ↔ z.2 = 0) ∧
      (∀ z ∈ A ×ˢ J,v z ∈ frontier W ↔ a z.1 ∈ frontier W) ∧
      (∀ z ∈ A ×ˢ J,P.productInverse (P.graph (v z)) = (P.graph (a z.1),ε*z.2)) ∧
      ∀ z ∈ A ×ˢ J,v z ∈ P.map '' (Disk ×ˢ J) ↔ a z.1 ∈ j '' Disk := by
  classical
  have hAc := hA.isCompact
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hA
  have haL : PolyhedralPLInCharts e a L.space := hLs.symm ▸ ha
  let b := P.graph ∘ a
  have hb : FinitePiecewiseAffineOn b A := hLs ▸ haL.finitePiecewiseAffineOn_comp L hL P.graph_PL
  have hbS : MapsTo b A (P.stars.marked 2).space :=
    fun z hz => P.surface_image.symm.subset ⟨a z,haS hz,rfl⟩
  obtain ⟨_,_,_,_,_,_,⟨_,⟨T,hT,hTs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) Band :=
    ⟨T,hT,hTs,T.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let q := P.product ∘ Prod.map b (id : ℝ → ℝ)
  have hparam : MapsTo (Prod.map b (id : ℝ → ℝ)) (A ×ˢ Band)
      ((P.stars.marked 2).space ×ˢ Band) := fun z hz => ⟨hbS hz.1,hz.2⟩
  have hq : FinitePiecewiseAffineOn q (A ×ˢ Band) := P.product_PL.comp (hb.prodMap hid) hparam
  have hqA : MapsTo q (A ×ˢ Band) P.stars.ambient.space :=
    fun z hz => P.product_mem_ambient (hparam hz)
  let f : V × ℝ → X := fun z => P.inverse (q z)
  have hf : PolyhedralPLInCharts e f (A ×ˢ Band) := by
    obtain ⟨M,hM,hMs,hMf⟩ := hq
    rw [←hMs]
    exact P.inverse_PL.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hMf⟩
      (fun z hz => hqA (hMs.subset hz))
  have hfcoords (z : V × ℝ) (hz : z ∈ A ×ˢ Band) :
      P.productInverse (P.graph (f z)) = (P.graph (a z.1),z.2) :=
    P.physical_product_inverse (haS hz.1) hz.2
  have hfi : InjOn f (A ×ˢ Band) := by
    intro z hz w hw heq
    have h := congrArg (fun x => P.productInverse (P.graph x)) heq
    rw [hfcoords z hz,hfcoords w hw] at h
    apply Prod.ext
    · apply hai hz.1 hw.1
      have hb := congrArg (fun z => (P.inverse z.1 : X)) h
      simpa only [P.inverse_graph _ (P.surface_carrier (haS hz.1)),
        P.inverse_graph _ (P.surface_carrier (haS hw.1))] using hb
    · exact congrArg (fun z : (s → ℝ × V3) × ℝ => z.2) h
  have hf0 (z : V) (hz : z ∈ A) : f (z,0) = a z := by
    change (P.inverse (P.product (b z,0)) : X) = a z
    rw [P.product_central _ (hbS hz)]
    exact P.inverse_graph _ (P.surface_carrier (haS hz))
  let f0 : A × Band → X := fun z => f ((z.1 : V),(z.2 : ℝ))
  have hf0c : Continuous f0 := hf.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.property,z.2.property⟩)
  let : CompactSpace A := isCompact_iff_compactSpace.mp hAc
  obtain ⟨δ,hδ,hδsmall,hthin⟩ := hf0c.exists_closed_strip_subset (hU.inter P.agreement_open) (by
    intro z
    change f ((z : V),0) ∈ U ∩ P.agreement
    rw [hf0 z z.property]
    exact ⟨haU ⟨z,z.property,rfl⟩,P.surface_in_agreement (haS z.property)⟩)
  let ε := min δ P.delta
  have hε : 0 < ε := lt_min hδ P.delta_pos
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεP : ε ≤ P.delta := min_le_right _ _
  have htime (t : ℝ) (ht : t ∈ J) : ε*t ∈ Band := by
    constructor <;> nlinarith [ht.1,ht.2,P.delta_le]
  let scale : ℝ →ᴬ[ℝ] ℝ := ε • ContinuousAffineMap.id ℝ ℝ
  obtain ⟨_,_,_,_,_,_,⟨_,⟨T',hT',hTs',_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  have hs : FinitePiecewiseAffineOn scale J := ⟨T',hT',hTs',T'.affineOnFaces_affine scale⟩
  have hId : FinitePiecewiseAffineOn (id : V → V) A :=
    ⟨L,hL,hLs,L.affineOnFaces_affine (ContinuousAffineMap.id ℝ V)⟩
  let r : V × ℝ → V × ℝ := Prod.map id scale
  have hr : FinitePiecewiseAffineOn r (A ×ˢ J) := hId.prodMap hs
  have hrmap : MapsTo r (A ×ˢ J) (A ×ˢ Band) := fun z hz => ⟨hz.1,htime z.2 hz.2⟩
  let v := f ∘ r
  have hv : PolyhedralPLInCharts e v (A ×ˢ J) := by
    obtain ⟨M,hM,hMs,hMf⟩ := hr
    rw [←hMs]
    exact hf.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hMf⟩
      (fun z hz => hrmap (hMs.subset hz))
  have hin (z : V × ℝ) (hz : z ∈ A ×ˢ J) :
      (P.graph (a z.1),ε*z.2) ∈ (P.stars.marked 2).space ×ˢ Band :=
    ⟨hbS hz.1,htime z.2 hz.2⟩
  have hvU (z : V × ℝ) (hz : z ∈ A ×ˢ J) : v z ∈ U ∩ P.agreement :=
    hthin ⟨z.1,hz.1⟩ ⟨ε*z.2,htime z.2 hz.2⟩ (by
      rw [abs_of_nonneg (mul_nonneg hε.le hz.2.1)]
      exact (mul_le_of_le_one_right hε.le hz.2.2).trans hεδ)
  refine ⟨ε,v,hε,hεP,fun _ => rfl,hv,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz w hw heq
    have h := hfi (hrmap hz) (hrmap hw) heq
    have hbase := congrArg (fun z : V × ℝ => z.1) h
    have hheight := congrArg (fun z : V × ℝ => z.2) h
    change z.1 = w.1 at hbase
    change ε*z.2 = ε*w.2 at hheight
    exact Prod.ext hbase (mul_left_cancel₀ hε.ne' hheight)
  · intro z hz
    exact ⟨⟨(P.product_domain _ (hin z hz)).mpr (mul_nonneg hε.le hz.2.1),
      P.region_subset (P.product_region _ (hin z hz))⟩,hvU z hz⟩
  · intro z hz
    change f (z,ε*0) = a z
    simpa only [mul_zero] using hf0 z hz
  · intro z hz
    change (P.inverse (P.product (P.graph (a z.1),ε*z.2)) : X) ∈ frontier D ↔ _
    rw [P.product_frontier _ (hin z hz),mul_eq_zero]
    exact or_iff_right hε.ne'
  · intro z hz
    rw [←P.frontier_agreement _ (hvU z hz).2]
    change (P.inverse (P.product (P.graph (a z.1),ε*z.2)) : X) ∈ frontier K ↔ _
    rw [P.product_boundary _ (hin z hz),P.inverse_graph _ (P.surface_carrier (haS hz.1))]
    exact P.frontier_agreement _ (P.surface_in_agreement (haS hz.1))
  · intro z hz
    exact P.physical_product_inverse (haS hz.1) (htime z.2 hz.2)
  · intro z hz
    change (P.inverse (P.product (P.graph (a z.1),ε*z.2)) : X) ∈ P.map '' (Disk ×ˢ J) ↔ _
    rw [P.physical_product_mem_cap_iff (haS hz.1) (htime z.2 hz.2)]
    exact and_iff_left ⟨mul_nonneg hε.le hz.2.1,
      (mul_le_of_le_one_right hε.le hz.2.2).trans hεP⟩

local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Base" => Set.prod Band J
local notation "Plus" => Set.prod (Set.prod J Band) J

theorem RelativeFrontierDiskProduct.exists_cap_quarter_box
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D W O K : Set X}
    {j : V2 → X} {s : Finset (D ∪ K : Set X)}
    (P : RelativeFrontierDiskProduct e D W O j K s)
    {a : P2 → X} (ha : PolyhedralPLInCharts e a Base) (hai : InjOn a Base)
    (haS : MapsTo a Base (frontier D ∩ W))
    (haW : ∀ z ∈ Base,a z ∈ frontier W ↔ z.2 = 0)
    (haCap : ∀ z ∈ Base,a z ∈ j '' Disk ↔ z.1 ≤ 0)
    {U : Set X} (hU : IsOpen U) (haU : a '' Base ⊆ U) :
    ∃ (ε : ℝ) (v : C3 → X),0 < ε ∧ ε ≤ P.delta ∧
      (∀ z,v z = P.inverse (P.product (P.graph (a (z.1.2,z.2)),ε*z.1.1))) ∧
      PolyhedralPLInCharts e v Plus ∧ InjOn v Plus ∧
      MapsTo v Plus (D ∩ W ∩ (U ∩ P.agreement)) ∧
      (∀ z ∈ Base,v ((0,z.1),z.2) = a z) ∧
      (∀ z ∈ Plus,v z ∈ frontier D ↔ z.1.1 = 0) ∧
      (∀ z ∈ Plus,v z ∈ frontier W ↔ z.2 = 0) ∧
      ∀ z ∈ Plus,v z ∈ P.map '' (Disk ×ˢ J) ↔ z.1.2 ≤ 0 := by
  have hBase := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨ε,k,hε,hεP,hkval,hk,hki,hkDW,hk0,hkD,hkW,_,hkCap⟩ :=
    P.exists_confined_base_extension hBase ha hai haS hU haU
  let L : C3 →L[ℝ] (P2 × ℝ) :=
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ)).prod
      (ContinuousLinearMap.snd ℝ P2 ℝ)).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ P2 ℝ))
  have hLval (z : C3) : L z = ((z.1.2,z.2),z.1.1) := rfl
  have hLmap : MapsTo L Plus (Base ×ˢ J) := fun z hz => ⟨⟨hz.1.2,hz.2⟩,hz.1.1⟩
  have hLf : FinitePiecewiseAffineOn L Plus := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨T,hT,hTs,_⟩,_⟩,_⟩ :=
      ((isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
        (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))).prod
        (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    exact ⟨T,hT,hTs,T.affineOnFaces_affine L.toContinuousAffineMap⟩
  let v := k ∘ L
  have hv : PolyhedralPLInCharts e v Plus := by
    obtain ⟨T,hT,hTs,hTf⟩ := hLf
    rw [←hTs]
    exact hk.comp_finitePiecewiseAffineOn T hT ⟨T,hT,rfl,hTf⟩
      (fun z hz => hLmap (hTs.subset hz))
  refine ⟨ε,v,hε,hεP,fun z => hkval (L z),hv,?_,fun z hz => hkDW (hLmap hz),?_,?_,?_,?_⟩
  · intro z hz w hw heq
    have hh := hki (hLmap hz) (hLmap hw) heq
    have ht := congrArg (fun z : P2 × ℝ => z.2) hh
    have hb := congrArg (fun z : P2 × ℝ => z.1.1) hh
    have hs := congrArg (fun z : P2 × ℝ => z.1.2) hh
    exact Prod.ext (Prod.ext ht hb) hs
  · intro z hz
    exact hk0 z hz
  · intro z hz
    exact hkD (L z) (hLmap hz)
  · intro z hz
    exact (hkW (L z) (hLmap hz)).trans (haW (z.1.2,z.2) ⟨hz.1.2,hz.2⟩)
  · intro z hz
    exact (hkCap (L z) (hLmap hz)).trans (haCap (z.1.2,z.2) ⟨hz.1.2,hz.2⟩)

theorem RelativeFrontierDiskProduct.exists_cap_side_box
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D W O K : Set X}
    {j : V2 → X} {s : Finset (D ∪ K : Set X)}
    (P : RelativeFrontierDiskProduct e D W O j K s)
    {a : P2 → X} (ha : PolyhedralPLInCharts e a (Band ×ˢ Band))
    (hai : InjOn a (Band ×ˢ Band)) (haS : MapsTo a (Band ×ˢ Band) (frontier D ∩ W))
    (haW : ∀ z ∈ Band ×ˢ Band,a z ∉ frontier W)
    (haCap : ∀ z ∈ Band ×ˢ Band,a z ∈ j '' Disk ↔ z.1 ≤ 0)
    {U : Set X} (hU : IsOpen U) (haU : a '' (Band ×ˢ Band) ⊆ U) :
    ∃ (ε : ℝ) (v : C3 → X),0 < ε ∧ ε ≤ P.delta ∧
      (∀ z,v z = P.inverse (P.product (P.graph (a z.1),ε*z.2))) ∧
      PolyhedralPLInCharts e v ((Band ×ˢ Band) ×ˢ J) ∧
      InjOn v ((Band ×ˢ Band) ×ˢ J) ∧
      MapsTo v ((Band ×ˢ Band) ×ˢ J) ((D ∩ W ∩ (U ∩ P.agreement)) \ frontier W) ∧
      (∀ z ∈ Band ×ˢ Band,v (z,0) = a z) ∧
      (∀ z ∈ (Band ×ˢ Band) ×ˢ J,v z ∈ frontier D ↔ z.2 = 0) ∧
      ∀ z ∈ (Band ×ˢ Band) ×ˢ J,v z ∈ P.map '' (Disk ×ˢ J) ↔ z.1.1 ≤ 0 := by
  have hi := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨ε,v,hε,hεP,hvval,hv,hvi,hvDW,hv0,hvD,hvW,_,hvCap⟩ :=
    P.exists_confined_base_extension (hi.prod hi) ha hai haS hU haU
  refine ⟨ε,v,hε,hεP,hvval,hv,hvi,?_,hv0,hvD,?_⟩
  · intro z hz
    exact ⟨hvDW hz,fun h => haW z.1 hz.1 ((hvW z hz).mp h)⟩
  · intro z hz
    exact (hvCap z hz).trans (haCap z.1 hz.1)

end PoincareConjecture.M76
