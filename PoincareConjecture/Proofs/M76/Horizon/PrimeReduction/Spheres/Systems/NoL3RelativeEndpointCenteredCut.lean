import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeCenteredComparison
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapCollarSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapOrientedCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalRelativeCenteredCollar
import Mathlib.Algebra.Order.Group.Pointwise.Interval








set_option autoImplicit false
open Set Metric Geometry
open scoped Pointwise
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_selected_endpoint_relative_centered_noL3_cut
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R U S T V : Set X}
    (s : ChartwisePLSphere e S) (sT : ChartwisePLSphere e T)
    (hR : IsCompact R) (he : PLDomain e R)
    (hU : PLDomain e U) (hUc : IsConnected U) (hUR : U ⊆ interior R)
    (hfrontU : frontier U = S ∪ T) (hST : Disjoint S T)
    (hV : IsOpen V) (hSV : S ⊆ V)
    (hno : HasNoPuncturedSphereComponents e f (R \ interior U))
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    ∃ (c : V3 × ℝ → X) (ε : ℝ),
      PolyhedralPLInCharts e c (Sphere ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn c (Sphere ×ˢ Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ Sphere, c (x,0) = s.map x) ∧
      0 < ε ∧ ε ≤ 1 / 24 ∧
      MapsTo c (Sphere ×ˢ Icc (-ε) ε) (V ∩ interior R) ∧
      (∀ η : ℝ, 0 < η → η ≤ ε → IsOpen (c '' (Sphere ×ˢ Ioo (-η) η))) ∧
      HasNoPuncturedSphereComponents e f (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) ∧
      ∃ (D : Bool → Set X) (_sD : ∀ i, ChartwisePLSphere e (D i))
        (W : (Sphere × unitInterval) ≃ₜ closure (c '' (Sphere ×ˢ Ioo (-ε) ε))),
        IsCompact (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) ∧
        PLDomain e (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) ∧
        Pairwise (fun i j => Disjoint (D i) (D j)) ∧
        (∀ i, D i ⊆ closure (c '' (Sphere ×ˢ Ioo (-ε) ε))) ∧
        frontier (c '' (Sphere ×ˢ Ioo (-ε) ε)) = D false ∪ D true ∧
        frontier (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) = frontier R ∪ ⋃ i, D i ∧
        closure (c '' (Sphere ×ˢ Ioo (-ε) ε)) ⊆ interior R ∧
        (∀ z, (W z : X) ∈ c '' (Sphere ×ˢ Ioo (-ε) ε) ↔
          (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1 / 2) ∧
        S ⊆ closure (c '' (Sphere ×ˢ Ioo (-ε) ε)) := by
  classical
  have hSR : S ⊆ interior R :=
    (subset_union_left.trans hfrontU.symm.subset).trans (hU.closed.frontier_subset.trans hUR)
  obtain ⟨t,F,N,HB,c0,δ,positive,hFc,hF,hFi,hNF,hN,hc0,hci0,hzero,_,hδ,hδsmall,
    hsmall,hopen,hout,hin,_⟩ := s.exists_selected_cap_exterior_half_collar
      hR he hSR hU hfrontU sT.isCompact.isClosed hST hV hSV
  have hzeroimage : c0 '' (N.space ×ˢ {(0 : ℝ)}) = S := by
    apply Subset.antisymm
    · rintro _ ⟨z,⟨hz,hz0⟩,rfl⟩
      have hz0' : z.2 = 0 := hz0
      rw [show z = (z.1,0) from Prod.ext rfl hz0',hzero ⟨z.1,hz⟩]
      exact (HB ⟨z.1,hz⟩).property
    · intro x hx
      refine ⟨((HB.symm ⟨x,hx⟩ : t → ℝ × V3),0),⟨(HB.symm ⟨x,hx⟩).property,rfl⟩,?_⟩
      exact (hzero _).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x,hx⟩))
  have hi0 : InjOn c0 (N.space ×ˢ Icc (-1 : ℝ) 1) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hci0.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  obtain ⟨c,hc,hci,hcz,himage⟩ := s.exists_original_oriented_centered_product_coordinates
    he.compatible N hN c0 hc0 hi0 hzeroimage positive
  have hclosed : ∀ a : ℝ, c '' (Sphere ×ˢ Icc (-a) a) = c0 '' (N.space ×ˢ Icc (-a) a) := by
    intro a
    rw [himage]
    cases positive <;> simp [image_neg_eq_neg]
  have hopenimage : ∀ a : ℝ, c '' (Sphere ×ˢ Ioo (-a) a) = c0 '' (N.space ×ˢ Ioo (-a) a) := by
    intro a
    rw [himage]
    cases positive <;> simp [image_neg_eq_neg]
  have hout' : Disjoint (c '' (Sphere ×ˢ Ioc 0 δ)) U := by
    rw [himage]
    cases positive <;> simpa [image_neg_eq_neg] using hout
  have hin' : c '' (Sphere ×ˢ Ico (-δ) 0) ⊆ interior U := by
    rw [himage]
    cases positive <;> simpa [image_neg_eq_neg] using hin
  have hsmall' : MapsTo c (Sphere ×ˢ Icc (-δ) δ) (V ∩ Tᶜ ∩ interior R) := by
    intro z hz
    obtain ⟨w,hw,hval⟩ := (hclosed δ).subset (mem_image_of_mem c hz)
    exact hval ▸ hsmall hw
  have hinclosed : MapsTo c (Sphere ×ˢ Icc (-δ) 0) U := by
    intro z hz
    rcases lt_or_eq_of_le hz.2.2 with ht | ht
    · exact interior_subset (hin' ⟨z,⟨hz.1,hz.2.1,ht⟩,rfl⟩)
    · rw [show z = (z.1,0) from Prod.ext rfl ht,hcz _ hz.1,s.map_eq ⟨z.1,hz.1⟩]
      exact hU.closed.frontier_subset (hfrontU.symm.subset
        (Or.inl (s.parametrization ⟨z.1,hz.1⟩).property))
  have hp : ∃ p ∈ U, p ∉ interior U ∧ p ∉ c '' (Sphere ×ˢ Icc (-δ) δ) := by
    obtain ⟨p,hpT⟩ := sT.isConnected.nonempty
    have hpfront : p ∈ frontier U := hfrontU.symm.subset (Or.inr hpT)
    refine ⟨p,hU.closed.frontier_subset hpfront,hpfront.2,?_⟩
    rintro ⟨z,hz,rfl⟩
    exact (hsmall' hz).1.2 hpT
  have hopen' (a : ℝ) (ha : 0 < a) (haδ : a ≤ δ) :
      IsOpen (c '' (Sphere ×ˢ Ioo (-a) a)) := by
    rw [hopenimage]
    exact hopen a ha haδ
  have hNc : IsCompact N.space := hNF.symm ▸ s.isCompact.image hFc
  obtain ⟨D,sD,W,hcompact,hPL',hdis,hDsub,hOf,hfront',hclosure,hWO,hWS,hSC⟩ :=
    s.original_relative_centered_collar_cut hR he F hF (hFi.mono (hSR.trans interior_subset))
      hNF hNc c0 hc0 hi0 (by positivity : 0 < δ/12) (by linarith : δ/12 < 1)
      (fun z hz => (hsmall ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩).2)
      (hopen (δ/12) (by positivity) (by linarith)) hzeroimage.symm
  obtain ⟨hQ,hPL,_,_,hfrontQ⟩ := he.interior_removal_geometry hR hU hUR
  let B : Bool → Set X := fun b => if b then T else S
  let sB : ∀ b, ChartwisePLSphere e (B b) := fun b => by
    cases b
    · exact s
    · exact sT
  have hBdis : Pairwise fun a b => Disjoint (B a) (B b) := by
    intro a b hab
    cases a <;> cases b <;> first | contradiction | exact hST | exact hST.symm
  have hBfront : frontier (R \ interior U) = frontier R ∪ ⋃ i, B i := by
    rw [show R \ interior U = R ∩ (interior U)ᶜ from rfl,hfrontQ,hfrontU]
    ext x
    simp only [B,mem_union,mem_iUnion,Bool.exists_bool,ite_true,ite_false,Bool.false_eq_true]
    tauto
  have hBinside (b) : B b ⊆ interior R := by
    apply Subset.trans _ (hU.closed.frontier_subset.trans hUR)
    rw [hfrontU]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  refine ⟨c,δ/12,hc,hci,hcz,by positivity,by linarith,?_,?_,?_,?_⟩
  · intro z hz
    have hm := hsmall' ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
    exact ⟨hm.1.1,hm.2⟩
  · intro a ha haδ
    exact hopen' a ha (by linarith)
  · rw [←neg_div]
    exact hno.selected_endpoint_centered_cut_relative hQ hPL B sB hBdis hBfront hBinside
      hUc (hUR.trans interior_subset) c hc hci hδ (by linarith)
      (fun _ hz => (hsmall' hz).2) hinclosed
      (fun z hz => hin' (mem_image_of_mem c hz)) hout'
      (by simpa only [neg_div] using hopen' (δ/12) (by positivity) (by linarith)) hp
      (by simpa only [←hopenimage (δ/12),neg_div] using hcompact)
      (by simpa only [←hopenimage (δ/12),neg_div] using hPL')
      D sD (fun i => (hDsub i).trans hclosure)
      (by simpa only [←hopenimage (δ/12),neg_div] using hfront')
      L g hf hg hgi hreal
  · rw [hopenimage (δ/12)]
    let H := s.parametrization.trans HB.symm
    let W' := (H.prodCongr (Homeomorph.refl unitInterval)).trans W
    exact ⟨D,sD,W',hcompact,hPL',hdis,hDsub,hOf,hfront',hclosure,
      fun z => hWO (H z.1,z.2),fun z => hWS (H z.1,z.2),hSC⟩

end PoincareConjecture.M76
