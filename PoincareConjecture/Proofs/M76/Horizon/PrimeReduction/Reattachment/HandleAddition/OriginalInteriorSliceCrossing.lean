import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.RegularInteriorHeightChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalProductHeightExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSpherePairCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

private noncomputable def interiorSurfaceCoordinateOrder : V3 ≃ᴬ[ℝ] C3 :=
  let L : V3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x 1,x 2),x 0)
      invFun := fun z => ![z.2,z.1.1,z.1.2]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  L.toContinuousLinearEquiv.toContinuousAffineEquiv

theorem OriginalDiskProduct.exists_local_regular_interior_crossings
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (he : ∀i k,(e i).symm.trans (e k)∈piecewiseAffineGroupoid V3)
    (hcover : ∀x∈S,∃i,x∈(e i).source)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D2×ˢIoo (-1:ℝ) 1))))
    {z : V2×ℝ} (hz : z∈D2×ˢIoo (-1:ℝ) 1)
    (hzS : P.map z∈S) :
    ∃ (O : Set X) (W : Set ℝ),
      IsOpen O ∧ P.map z∈O ∧ W.Finite ∧
      ∀t∈I,∀y∈O∩S,y∈interior R → y∈P.slice t '' D2 → t∉W →
        Nonempty (OriginalSurfacePairChart e (S∩R) (P.slice t '' D2) y false) := by
  classical
  obtain ⟨Q,hzQ,_,hQ,hQS⟩ := s.exists_pair_chart he hcover hzS
  obtain ⟨f,U,O,hU,hf,hO,hzO,hOQ,hQU,hlevel,_⟩ :=
    P.exists_local_height_extension hopen Q hQ hz hzQ
  let A := interiorSurfaceCoordinateOrder
  have hAPL : LocallyPiecewiseAffineOn A univ :=
    locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ
  have hAiPL : LocallyPiecewiseAffineOn A.symm univ :=
    locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ
  have hUA : IsOpen (A.symm ⁻¹' U) := hU.preimage A.symm.continuous
  have hFA : LocallyPiecewiseAffineOn (f ∘ A.symm) (A.symm ⁻¹' U) := by
    simpa using hf.comp hAiPL
  have hzUA : A (Q (P.map z))∈A.symm ⁻¹' U := by
    change A.symm (A (Q (P.map z)))∈U
    rw [A.symm_apply_apply]
    exact hQU ⟨P.map z,hzO,rfl⟩
  obtain ⟨V,W,hV,hzV,hVU,hW,hcharts⟩ :=
    SimplicialComplex.exists_regular_height_charts_preserving_plane hFA hzUA
  let O' := O ∩ (Q.source ∩ Q ⁻¹' (A ⁻¹' V))
  have hO' : IsOpen O' := hO.inter
    (Q.isOpen_inter_preimage (hV.preimage A.continuous))
  have hzO' : P.map z∈O' := ⟨hzO,hzQ,hzV⟩
  refine ⟨O',W,hO',hzO',hW,?_⟩
  intro t ht y hy hyint hyt htW
  have hyO := hy.1.1
  have hyQ : y∈Q.source := hy.1.2.1
  have hfy : f (Q y)=t := ((hlevel t ht y hyO).mp hyt).2
  have hAy : (A (Q y)).2=0 := (hQS y hyQ).mp hy.2
  obtain ⟨H,hyH,hHy,hHV,hH,hplane,hheight⟩ := hcharts (A (Q y)) hy.1.2.2 hAy
    (by simpa only [Function.comp_apply,A.symm_apply_apply,hfy] using htW)
  let C₀ := A.toHomeomorph.toOpenPartialHomeomorph.trans H
  let V₀ := Q.target ∩ Q.symm ⁻¹' (O'∩interior R)
  have hV₀ : IsOpen V₀ := Q.symm.isOpen_inter_preimage (hO'.inter isOpen_interior)
  let C := C₀.restrOpen V₀ hV₀
  have hyC : Q y∈C.source := by
    refine ⟨⟨mem_univ _,hyH⟩,Q.map_source hyQ,?_⟩
    change Q.symm (Q y)∈O'∩interior R
    rw [Q.left_inv hyQ]
    exact ⟨hy.1,hyint⟩
  have hCs : C.source⊆Q.target := fun _ hx => hx.2.1
  have hC₀PL : LocallyPiecewiseAffineOn C₀ C₀.source := by
    exact hH.1.comp hAPL
  have hC₀iPL : LocallyPiecewiseAffineOn C₀.symm C₀.target := by
    exact hAiPL.comp hH.2
  refine ⟨OriginalSurfacePairChart.of_interior_planes Q C hQ hyQ hyC hHy hCs
    (hC₀PL.mono C.open_source inter_subset_left)
    (hC₀iPL.mono C.open_target inter_subset_left) ?_ ?_⟩
  · intro q hq
    have hqO' : Q.symm q∈O' := hq.2.2.1
    have hqQ : Q.symm q∈Q.source := Q.map_target hq.2.1
    have hqR : Q.symm q∈R := interior_subset hq.2.2.2
    have hh := hQS (Q.symm q) hqQ
    rw [Q.right_inv hq.2.1] at hh
    change Q.symm q∈S∩R ↔ (H (A q)).2=0
    rw [hplane (A q) hq.1.2]
    exact (and_iff_left hqR).trans hh
  · intro q hq
    have hqO' : Q.symm q∈O' := hq.2.2.1
    have hqR : Q.symm q∈R := interior_subset hq.2.2.2
    have hh := hlevel t ht (Q.symm q) hqO'.1
    rw [Q.right_inv hq.2.1] at hh
    change Q.symm q∈P.slice t '' D2 ↔ (H (A q)).1.1=0
    rw [hheight (A q) hq.1.2]
    simp only [Function.comp_apply,A.symm_apply_apply,hfy]
    exact hh.trans ((and_iff_right hqR).trans sub_eq_zero.symm)

theorem OriginalDiskProduct.exists_regular_interior_crossing_heights
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (he : ∀i k,(e i).symm.trans (e k)∈piecewiseAffineGroupoid V3)
    (hcover : ∀x∈S,∃i,x∈(e i).source)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D2×ˢIoo (-1:ℝ) 1)))) :
    ∃ W : Set ℝ,W.Finite ∧
      ∀t∈Icc (-(1/2):ℝ) (1/2),t∉W →
        ∀y∈S∩interior R,y∈P.slice t '' D2 →
          Nonempty (OriginalSurfacePairChart e (S∩R) (P.slice t '' D2) y false) := by
  classical
  let J := Icc (-(1/2):ℝ) (1/2)
  have hJI : J⊆I := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hJopen : J⊆Ioo (-1:ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  let C := S∩P.map '' (D2×ˢJ)
  have hcompact : IsCompact C :=
    (((isCompact_closedBall (0:V2) 1).prod isCompact_Icc).image_of_continuousOn
      (P.polyhedral.continuousOn.mono (fun z hz => ⟨hz.1,hJI hz.2⟩))).inter_left
        s.isCompact.isClosed
  have hlocal (x:C) : ∃ (O:Set X) (W:Set ℝ),
      IsOpen O ∧ (x:X)∈O ∧ W.Finite ∧
      ∀t∈I,∀y∈O∩S,y∈interior R → y∈P.slice t '' D2 → t∉W →
        Nonempty (OriginalSurfacePairChart e (S∩R) (P.slice t '' D2) y false) := by
    obtain ⟨z,hz,hzx⟩ := x.property.2
    have hzS : P.map z∈S := hzx.symm ▸ x.property.1
    obtain ⟨O,W,hO,hzO,hW,hcross⟩ := P.exists_local_regular_interior_crossings
      s he hcover hopen ⟨hz.1,hJopen hz.2⟩ hzS
    exact ⟨O,W,hO,hzx ▸ hzO,hW,hcross⟩
  choose O W hO hxO hW hcross using hlocal
  obtain ⟨F,hF⟩ := hcompact.elim_finite_subcover O hO
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxO ⟨x,hx⟩⟩)
  let W₀ := ⋃i∈F,W i
  refine ⟨W₀,F.finite_toSet.biUnion (fun i _ => hW i),?_⟩
  intro t ht htW y hy hyt
  have hyC : y∈C := by
    obtain ⟨z,hz,hzy⟩ := hyt
    exact ⟨hy.1,(z,t),⟨hz,ht⟩,hzy⟩
  obtain ⟨i,hi,hyO⟩ := mem_iUnion₂.mp (hF hyC)
  exact hcross i t (hJI ht) y ⟨hyO,hy.1⟩ hy.2 hyt
    (fun htWi => htW (mem_iUnion₂.mpr ⟨i,hi,htWi⟩))

end PoincareConjecture.M76
