import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage

set_option autoImplicit false
open Set Metric Geometry Topology
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "T3" => (V2 × ℝ)

theorem OriginalDiskProduct.exists_local_inverse_extension
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {z : T3} (hz : z ∈ D2 ×ˢ Ioo (-1 : ℝ) 1) (hzQ : P.map z ∈ Q.source) :
    ∃ (q : V3 → T3) (U : Set V3) (O : Set X),
      IsOpen U ∧ LocallyPiecewiseAffineOn q U ∧
      IsOpen O ∧ P.map z ∈ O ∧ O ⊆ Q.source ∧ Q '' O ⊆ U ∧
      (∀ x ∈ O ∩ R,q (Q x) ∈ D2 ×ˢ I ∧ P.map (q (Q x)) = x) ∧
      ∀ w ∈ D2 ×ˢ I,P.map w ∈ O → q (Q (P.map w)) = w := by
  classical
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  have hzK : z ∈ K.space := hKs.symm.subset ⟨hz.1,Ioo_subset_Icc_self hz.2⟩
  have hPK : PolyhedralPLInCharts e P.map K.space := hKs.symm ▸ P.polyhedral
  obtain ⟨N,W,hN,hNK,hW,hzW,hWN,hNQ,hcoords⟩ :=
    hPK.exists_finite_compatible_chart_patch K hK Q hQ ⟨z,hzK⟩ hzQ
  have hzi : z ∈ N.space := hWN ⟨⟨z,hzK⟩,hzW,rfl⟩
  have hci : InjOn (Q ∘ P.map) N.space := by
    intro x hx y hy hxy
    exact P.injective (hKs.subset (hNK hx)) (hKs.subset (hNK hy))
      (Q.injOn (hNQ hx) (hNQ hy) hxy)
  obtain ⟨H,hH,hHval⟩ := hcoords.exists_homeomorph_image hci
  obtain ⟨r,hr,hrval⟩ := hH.symm
  have hrleft (x : T3) (hx : x ∈ N.space) : r (Q (P.map x)) = x := by
    have hh := hrval (H ⟨x,hx⟩)
    rw [H.symm_apply_apply] at hh
    simpa only [hHval,Function.comp_apply] using hh.symm
  obtain ⟨q,U,hU,hQU,hq,hqr⟩ := hr.exists_locallyPiecewiseAffine_extension
  have hqleft (x : T3) (hx : x ∈ N.space) : q (Q (P.map x)) = x :=
    (hqr ⟨x,hx,rfl⟩).trans (hrleft x hx)
  let f : K.space → R := fun x => ⟨P.map x,P.inside (hKs.subset x.property)⟩
  have hfi : IsEmbedding f := by
    apply IsEmbedding.codRestrict
    rw [hKs]
    exact P.embedding.isEmbedding
  let V : Set K.space := W ∩ {x | (x : T3).2 ∈ Ioo (-1 : ℝ) 1}
  have hV : IsOpen V := hW.inter (isOpen_Ioo.preimage
    (continuous_snd.comp continuous_subtype_val))
  have hVrange : f '' V ⊆ (Subtype.val : R → X) ⁻¹' (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)) := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,⟨(hKs.subset x.property).1,hx.2⟩,rfl⟩
  have hrange : (Subtype.val : R → X) ⁻¹' (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)) ⊆ range f := by
    rintro x ⟨w,hw,hwx⟩
    exact ⟨⟨w,hKs.symm.subset ⟨hw.1,Ioo_subset_Icc_self hw.2⟩⟩,Subtype.ext hwx⟩
  have hFV : IsOpen (f '' V) := hfi.isInducing.isOpen_image_of_subset_open hV hopen hVrange hrange
  obtain ⟨O₀,hO₀,hOeq⟩ := isOpen_induced_iff.mp hFV
  have hzO₀ : P.map z ∈ O₀ := by
    change (f ⟨z,hzK⟩) ∈ (Subtype.val : R → X) ⁻¹' O₀
    rw [hOeq]
    exact ⟨⟨z,hzK⟩,⟨hzW,hz.2⟩,rfl⟩
  let O := O₀ ∩ (Q.source ∩ Q ⁻¹' U)
  have hO : IsOpen O := hO₀.inter (Q.isOpen_inter_preimage hU)
  have hzO : P.map z ∈ O := ⟨hzO₀,hzQ,hQU ⟨z,hzi,rfl⟩⟩
  have hOR (x : X) (hx : x ∈ O ∩ R) :
      q (Q x) ∈ D2 ×ˢ I ∧ P.map (q (Q x)) = x := by
    have hxV : (⟨x,hx.2⟩ : R) ∈ f '' V := by
      rw [←hOeq]
      exact hx.1.1
    obtain ⟨y,hy,hyx⟩ := hxV
    have hyv : P.map y = x := congrArg Subtype.val hyx
    rw [←hyv,hqleft y (hWN ⟨y,hy.1,rfl⟩)]
    exact ⟨hKs.subset y.property,rfl⟩
  refine ⟨q,U,O,hU,hq,hO,hzO,fun x hx => hx.2.1,?_,hOR,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact hx.2.2
  · intro w hw hwO
    have hh := hOR (P.map w) ⟨hwO,P.inside hw⟩
    exact P.injective hh.1 hw hh.2

theorem OriginalDiskProduct.exists_local_height_extension
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {z : T3} (hz : z ∈ D2 ×ˢ Ioo (-1 : ℝ) 1) (hzQ : P.map z ∈ Q.source) :
    ∃ (f : V3 → ℝ) (U : Set V3) (O : Set X),
      IsOpen U ∧ LocallyPiecewiseAffineOn f U ∧
      IsOpen O ∧ P.map z ∈ O ∧ O ⊆ Q.source ∧ Q '' O ⊆ U ∧
      (∀ t ∈ I, ∀ x ∈ O,
        x ∈ (fun u : V2 => P.map (u,t)) '' D2 ↔ x ∈ R ∧ f (Q x) = t) ∧
      ∀ w ∈ D2 ×ˢ I,P.map w ∈ O → f (Q (P.map w)) = w.2 := by
  obtain ⟨q,U,O,hU,hq,hO,hzO,hOQ,hQU,hleft,hright⟩ :=
    P.exists_local_inverse_extension hopen Q hQ hz hzQ
  let f : V3 → ℝ := fun y => (q y).2
  have hf : LocallyPiecewiseAffineOn f U := by
    have hh := (locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap isOpen_univ).comp hq
    simpa [f,Function.comp_def] using hh
  refine ⟨f,U,O,hU,hf,hO,hzO,hOQ,hQU,?_,?_⟩
  · intro t ht x hx
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨P.inside ⟨hu,ht⟩,congrArg Prod.snd (hright (u,t) ⟨hu,ht⟩ hx)⟩
    · rintro ⟨hxR,hxt⟩
      obtain ⟨hqin,hqx⟩ := hleft x ⟨hx,hxR⟩
      refine ⟨(q (Q x)).1,hqin.1,?_⟩
      change (q (Q x)).2 = t at hxt
      simpa only [←hxt,Prod.eta] using hqx
  · intro w hw hwO
    exact congrArg Prod.snd (hright w hw hwO)

end PoincareConjecture.M76
