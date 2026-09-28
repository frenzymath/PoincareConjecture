import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereAnnulusParameter
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLSphere.exists_same_collar_coordinates
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {B : Set X}
    (s : ChartwisePLSphere e B)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (N.space ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) (side : Bool)
    (hB : B = c '' (N.space ×ˢ {if side then ε else -ε})) :
    ∃ F : V3 × ℝ → X, PolyhedralPLInCharts e F (Sphere ×ˢ I) ∧
      InjOn F (Sphere ×ˢ I) ∧
      F '' (Sphere ×ˢ I) = c '' (N.space ×ˢ Icc (-ε) ε) ∧
      (∀ x ∈ Sphere, F (x,1) = s.map x) ∧
      (∀ x ∈ Sphere, F (x,0) ∈ c '' (N.space ×ˢ {if side then -ε else ε})) ∧
      F '' (Sphere ×ˢ {(0 : ℝ)}) = c '' (N.space ×ˢ {if side then -ε else ε}) := by
  classical
  let δ := if side then ε else -ε
  have hδ : δ ∈ Icc (-1 : ℝ) 1 := by cases side <;> dsimp [δ] <;> constructor <;> linarith
  let A : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E δ)
  have hA : FinitePiecewiseAffineOn A N.space :=
    ⟨N,hN,rfl,N.affineOnFaces_affine A⟩
  have hslice : PolyhedralPLInCharts e (fun x => c (x,δ)) N.space :=
    hc.comp_finitePiecewiseAffineOn N hN hA (fun x hx => ⟨hx,hδ⟩)
  have hslicei : InjOn (fun x => c (x,δ)) N.space := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hci ⟨hx,hδ⟩ ⟨hy,hδ⟩ hxy)
  have hsimage : (fun x => c (x,δ)) '' N.space = B := by
    rw [hB]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(y,δ),⟨hy,rfl⟩,rfl⟩
    · rintro ⟨⟨y,t⟩,⟨hy,ht⟩,hval⟩
      have ht' : t = δ := ht
      exact ⟨y,hy,by simpa only [ht'] using hval⟩
  let : CompactSpace N.space := isCompact_iff_compactSpace.mp (N.isCompact_space_of_finite hN)
  let H0 : N.space ≃ₜ ((fun x => c (x,δ)) '' N.space) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn (fun x => c (x,δ)) N.space hslicei)
      (hslice.continuousOn.domRestrict.subtype_mk _)
  let H := H0.trans (Homeomorph.setCongr hsimage)
  have hHval (x : N.space) : (H x : X) = c ((x : E),δ) := rfl
  let q : V3 → E := fun x =>
    if hx : x ∈ Sphere then H.symm (s.parametrization ⟨x,hx⟩) else 0
  have hqval (x : Sphere) : q x = (H.symm (s.parametrization x) : E) := by
    simp only [q,dif_pos x.property]
  have hqN : MapsTo q Sphere N.space := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (H.symm (s.parametrization ⟨x,hx⟩)).property
  have hqcont : ContinuousOn q Sphere := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (H.symm.continuous.comp s.parametrization.continuous)
    convert h using 1
    funext x
    exact hqval x
  have hqtop (x : V3) (hx : x ∈ Sphere) : c (q x,δ) = s.map x := by
    rw [hqval ⟨x,hx⟩,← hHval,H.apply_symm_apply,s.map_eq ⟨x,hx⟩]
  obtain ⟨L,hL,hLS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hq : FinitePiecewiseAffineOn q Sphere := by
    have hcomp : PolyhedralPLInCharts e ((fun x => c (x,δ)) ∘ q) Sphere :=
      s.piecewiseAffine.congr (fun x hx => (hqtop x hx).symm)
    have h := hslice.finitePiecewiseAffineOn_lift hcompat hslicei L hL
      (hqcont.mono hLS.subset) (fun x hx => hqN (hLS.subset hx)) (hLS.symm ▸ hcomp)
    exact hLS ▸ h
  have hqi : InjOn q Sphere := by
    intro x hx y hy heq
    rw [hqval ⟨x,hx⟩,hqval ⟨y,hy⟩] at heq
    exact congrArg Subtype.val (s.parametrization.injective (H.symm.injective (Subtype.ext heq)))
  have hqonto : q '' Sphere = N.space := by
    apply Subset.antisymm (by rintro _ ⟨x,hx,rfl⟩; exact hqN hx)
    intro y hy
    let x := s.parametrization.symm (H ⟨y,hy⟩)
    refine ⟨x,x.property,?_⟩
    rw [hqval x,s.parametrization.apply_symm_apply,H.symm_apply_apply]
  let T : ℝ →ᴬ[ℝ] ℝ :=
    δ • (2 • ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ 1)
  have hTval (t : ℝ) : T t = (2*t-1)*δ := by simp [T,mul_comm]
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJI,_⟩,_⟩,_⟩ := isFinitePLBallPair_Icc zero_lt_one
  have hT : FinitePiecewiseAffineOn T I := ⟨J,hJ,hJI,J.affineOnFaces_affine T⟩
  let G := Prod.map q T
  have hG : FinitePiecewiseAffineOn G (Sphere ×ˢ I) := hq.prodMap hT
  have hTin (t : ℝ) (ht : t ∈ I) : T t ∈ Icc (-ε) ε := by
    rw [hTval]
    cases side <;> dsimp [δ] <;> constructor <;> nlinarith [ht.1,ht.2]
  have hGfull (z : V3 × ℝ) (hz : z ∈ Sphere ×ˢ I) : G z ∈ N.space ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨hqN hz.1,by change -1 ≤ T z.2; linarith [(hTin z.2 hz.2).1],
      by change T z.2 ≤ 1; linarith [(hTin z.2 hz.2).2]⟩
  let F := c ∘ G
  have hF : PolyhedralPLInCharts e F (Sphere ×ˢ I) := by
    obtain ⟨M,hM,hMS,hfaces⟩ := hG
    rw [← hMS]
    exact hc.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hfaces⟩
      (fun z hz => hGfull z (hMS.subset hz))
  have hδne : δ ≠ 0 := by cases side <;> dsimp [δ] <;> linarith
  have hFi : InjOn F (Sphere ×ˢ I) := by
    intro x hx y hy hxy
    have heq := hci (hGfull x hx) (hGfull y hy) hxy
    apply Prod.ext
    · exact hqi hx.1 hy.1 (congrArg Prod.fst heq)
    · have ht := congrArg Prod.snd heq
      change T x.2 = T y.2 at ht
      rw [hTval,hTval] at ht
      have ht' := mul_right_cancel₀ hδne ht
      linarith
  have hGimage : G '' (Sphere ×ˢ I) = N.space ×ˢ Icc (-ε) ε := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨hqN hz.1,hTin z.2 hz.2⟩
    · rintro ⟨y,t⟩ ⟨hy,ht⟩
      obtain ⟨x,hx,hqx⟩ := hqonto.symm.subset hy
      have hpos : 0 < 2*ε := by positivity
      have hcase (u : ℝ) (hu : u ∈ I) (hTu : T u = t) : (y,t) ∈ G '' (Sphere ×ˢ I) :=
        ⟨(x,u),⟨hx,hu⟩,Prod.ext hqx hTu⟩
      cases side
      · apply hcase ((ε-t)/(2*ε))
        · exact ⟨div_nonneg (by linarith [ht.2]) hpos.le,
            (div_le_iff₀ hpos).mpr (by linarith [ht.1])⟩
        · rw [hTval]
          dsimp [δ]
          field_simp
          ring
      · apply hcase ((t+ε)/(2*ε))
        · exact ⟨div_nonneg (by linarith [ht.1]) hpos.le,
            (div_le_iff₀ hpos).mpr (by linarith [ht.2])⟩
        · rw [hTval]
          dsimp [δ]
          field_simp
          ring
  refine ⟨F,hF,hFi,(image_image c G (Sphere ×ˢ I)).symm.trans
    (congrArg (image c) hGimage),?_,?_,?_⟩
  · intro x hx
    change c (q x,T 1) = s.map x
    simpa only [hTval,mul_one,sub_self,one_mul,show (2 : ℝ)-1=1 by norm_num] using hqtop x hx
  · intro x hx
    refine ⟨(q x,T 0),⟨hqN hx,?_⟩,rfl⟩
    change T 0 = _
    rw [hTval]
    cases side <;> simp [δ]
  · have hTzero : T 0 = if side then -ε else ε := by
      rw [hTval]
      cases side <;> simp [δ]
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(q z,T 0),⟨hqN hz,hTzero⟩,rfl⟩
    · rintro ⟨⟨y,t⟩,⟨hy,ht⟩,rfl⟩
      obtain ⟨z,hz,hqz⟩ := hqonto.symm.subset hy
      refine ⟨(z,0),⟨hz,rfl⟩,?_⟩
      change c (q z,T 0) = c (y,t)
      rw [hqz,hTzero,show t = (if side then -ε else ε) from ht]

end PoincareConjecture.M76
