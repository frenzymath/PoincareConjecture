import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNonvertexHeightChart
import PoincareConjecture.Proofs.M76.Mathlib.AffineLevelSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph










set_option autoImplicit false
open Set Geometry Metric
namespace Geometry.SimplicialComplex
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem exists_affine_height_frame_preserving_plane
    (ell : C3 →ᴬ[ℝ] ℝ) (w : C3)
    (hw : ell.contLinear w = 1) (hwplane : w.2 = 0) (x : C3) :
    ∃ F : C3 ≃ᴬ[ℝ] C3,
      F x = ((0,0),x.2) ∧
      (∀z,(F z).1.1=ell z-ell x) ∧ ∀z,(F z).2=z.2 := by
  let a := ell.contLinear ((1,0),0)
  let b := ell.contLinear ((0,1),0)
  have hexpand (z : ℝ × ℝ) : ell.contLinear (z,0)=z.1*a+z.2*b := by
    have hz : (z,(0:ℝ))=z.1 • (((1,0),0):C3)+z.2 • (((0,1),0):C3) := by
      ext <;> simp
    rw [hz,map_add,map_smul,map_smul]
    rfl
  have hab : a≠0 ∨ b≠0 := by
    by_contra h
    push Not at h
    have hh := hexpand w.1
    rw [←hwplane,hw,h.1,h.2] at hh
    norm_num at hh
  let side : C3 →ₗ[ℝ] ℝ := if a=0 then
    (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ×ℝ) ℝ) else
    (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ×ℝ) ℝ)
  let L := (ell.toAffineMap.linear.prod side).prod (LinearMap.snd ℝ (ℝ×ℝ) ℝ)
  have hLi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    have hzero : ell.contLinear z=0 := congrArg (fun q:C3 => q.1.1) hz
    have hside : side z=0 := congrArg (fun q:C3 => q.1.2) hz
    have hz2 : z.2=0 := congrArg Prod.snd hz
    have hx := hexpand z.1
    rw [←hz2,hzero] at hx
    apply Prod.ext _ hz2
    apply Prod.ext
    · by_cases ha : a=0
      · simpa [side,ha] using hside
      · have hzy : z.1.2=0 := by simpa [side,ha] using hside
        rw [hzy,zero_mul,add_zero] at hx
        exact (mul_eq_zero.mp hx.symm).resolve_right ha
    · by_cases ha : a=0
      · have hb : b≠0 := hab.resolve_left (not_not.mpr ha)
        rw [ha,mul_zero,zero_add] at hx
        exact (mul_eq_zero.mp hx.symm).resolve_right hb
      · simpa [side,ha] using hside
  let E := (LinearEquiv.ofBijective L
    ⟨hLi,LinearMap.injective_iff_surjective.mp hLi⟩).toContinuousLinearEquiv.toContinuousAffineEquiv
  let F := E.trans (ContinuousAffineEquiv.constVAdd ℝ C3 ((-ell.contLinear x,-side x),0))
  refine ⟨F,?_,?_,?_⟩
  · change ((-ell.contLinear x+ell.contLinear x,-side x+side x),0+x.2)=_
    simp
  · intro z
    change -ell.contLinear x+ell.contLinear z=ell z-ell x
    have hx := ell.contLinear_map_vsub x 0
    have hz := ell.contLinear_map_vsub z 0
    simp only [vsub_eq_sub,sub_zero] at hx hz
    rw [hx,hz]
    ring
  · intro z
    change 0+z.2=z.2
    exact zero_add _

theorem exists_nonvertex_height_chart_preserving_plane
    (K : SimplicialComplex ℝ C3) (hK : K.faces.Finite)
    {f : C3 → ℝ} (hf : K.AffineOnFaces f) {x : C3}
    (hx : x ∈ interior K.space) (hreg : ∀v∈K.vertices,f v≠f x)
    (B : SimplicialComplex ℝ C3) (hBK : B≤K) (hxB : x∈B.space)
    (hzero : ∀z∈B.space,z.2=0) :
    ∃ H : OpenPartialHomeomorph C3 C3,
      x∈H.source ∧ H x=0 ∧ H.source⊆interior K.space ∧
      H∈piecewiseAffineGroupoid C3 ∧
      (∀z∈H.source,(H z).2=z.2) ∧
      ∀z∈H.source,(H z).1.1=f z-f x := by
  let psi := (ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ).toContinuousAffineMap
  obtain ⟨ell,w,T,hellw,hpsiw,hxT,hTx,hTs,_,hT,hheight,hpsi,_⟩ :=
    K.exists_nonvertex_height_chart_preserving_affine hK hf hx hreg B hBK hxB psi
      (fun z hz => (hzero z hz).trans (hzero x hxB).symm)
  obtain ⟨F,hFx,hFheight,hFplane⟩ :=
    exists_affine_height_frame_preserving_plane ell w hellw hpsiw x
  let H := T.trans F.toHomeomorph.toOpenPartialHomeomorph
  have hHs : H.source=T.source := by
    change T.source∩T ⁻¹' univ=T.source
    simp
  have hellx : ell x=f x := by simpa only [hTx] using hheight x hxT
  refine ⟨H,hHs.symm.subset hxT,?_,hHs.subset.trans hTs,?_,?_,?_⟩
  · change F (T x)=0
    rw [hTx,hFx,hzero x hxB]
    rfl
  · exact (piecewiseAffineGroupoid _).trans hT
      ⟨locallyPiecewiseAffineOn_affine F.toContinuousAffineMap isOpen_univ,
        locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap isOpen_univ⟩
  · intro z _
    exact (hFplane (T z)).trans (hpsi z)
  · intro z hz
    exact (hFheight (T z)).trans (by rw [hheight z (hHs.subset hz),hellx])

theorem exists_regular_height_charts_preserving_plane
    {f : C3 → ℝ} {U : Set C3}
    (hf : LocallyPiecewiseAffineOn f U) {x : C3} (hx : x∈U) :
    ∃ (V : Set C3) (W : Set ℝ),
      IsOpen V ∧ x∈V ∧ V⊆U ∧ W.Finite ∧
      ∀y∈V,y.2=0 → f y∉W →
        ∃ H : OpenPartialHomeomorph C3 C3,
          y∈H.source ∧ H y=0 ∧ H.source⊆V ∧
          H∈piecewiseAffineGroupoid C3 ∧
          (∀z∈H.source,(H z).2=z.2) ∧
          ∀z∈H.source,(H z).1.1=f z-f y := by
  classical
  let a := (LinearMap.snd ℝ (ℝ×ℝ) ℝ).toAffineMap
  obtain ⟨K,hK,hxK,hKU,hfK⟩ := hf x hx
  let N := hK.toFinset.sup Finset.card
  have hN (s) (hs : s∈K.faces) : s.card≤N+1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L,hL,hLK,_,halign⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hN {a}
  have ha : L.RespectsAffineHyperplane a := halign a (by simp)
  let B := L.affineZeroSubcomplex a
  have hBL : B≤L := fun _ hs => hs.1
  have hBs : B.space=L.space∩{z | a z=0} := L.affineZeroSubcomplex_space a ha
  refine ⟨interior L.space,f '' L.vertices,isOpen_interior,?_,?_,
    (L.finite_vertices_of_finite_faces hL).image f,?_⟩
  · rwa [hLK.space_eq]
  · rw [hLK.space_eq]
    exact interior_subset.trans hKU
  · intro y hy hyzero hyW
    have hyB : y∈B.space := hBs.symm.subset ⟨interior_subset hy,hyzero⟩
    exact L.exists_nonvertex_height_chart_preserving_plane hL
      (hLK.affineOnFaces hfK) hy (fun v hv h => hyW ⟨v,hv,h⟩)
      B hBL hyB (fun z hz => (hBs.subset hz).2)

end Geometry.SimplicialComplex

