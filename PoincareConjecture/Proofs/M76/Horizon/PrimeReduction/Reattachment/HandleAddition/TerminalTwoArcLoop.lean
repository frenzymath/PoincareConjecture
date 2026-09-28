import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.SquareRimHalves
import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval


set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
open Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

private theorem interval_mem_endpoints
    {X : Type*} [TopologicalSpace X] {U : Set X} {a b : X}
    (p : I01 ≃ₜ U) (h0 : (p (0 : unitInterval) : X) = a)
    (h1 : (p (1 : unitInterval) : X) = b) (t : I01) :
    (p t : X) ∈ ({a,b} : Set X) ↔ t = 0 ∨ t = 1 := by
  rw [←h0,←h1]
  simp only [mem_insert_iff,mem_singleton_iff,Subtype.coe_inj,p.injective.eq_iff]

theorem exists_two_arc_loop
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} {a b : X} (hUV : U ∩ V = {a,b})
    (p : I01 ≃ₜ U) (q : I01 ≃ₜ V)
    (hp0 : (p (0 : unitInterval) : X) = a) (hp1 : (p (1 : unitInterval) : X) = b)
    (hq0 : (q (0 : unitInterval) : X) = a) (hq1 : (q (1 : unitInterval) : X) = b) :
    ∃ gamma : C(Q2,X), Function.Injective gamma ∧ range gamma = U ∪ V ∧
      (∀ t : I01, gamma (squareRimLoop (squareRimHalfTime false t)) = p t) ∧
      (∀ t : I01, gamma (squareRimLoop (squareRimHalfTime true t)) = q t) := by
  let p0 := squareRimHalfChart false
  let p1 := squareRimHalfChart true
  let e := p0.symm.trans p
  let f := p1.symm.trans q
  have hoverlap (x : squareRimHalfCarrier false) :
      (x : V2) ∈ squareRimHalfCarrier true ↔ (e x : X) ∈ V := by
    obtain ⟨t,rfl⟩ := p0.surjective x
    have hleft : (p0 t : V2) ∈ squareRimHalfCarrier true ↔
        (p0 t : V2) ∈ ({(squareRimBase : V2),(squareRimVertex 2 : V2)} : Set V2) := by
      rw [←squareRimHalfCarrier_inter]
      simp only [mem_inter_iff,(p0 t).property,true_and]
    have hright : (p t : X) ∈ V ↔ (p t : X) ∈ ({a,b} : Set X) := by
      rw [←hUV]
      simp only [mem_inter_iff,(p t).property,true_and]
    simpa only [e,Homeomorph.trans_apply,p0.symm_apply_apply] using
      hleft.trans ((interval_mem_endpoints p0 (by simp [p0]) (by simp [p0]) t).trans
        ((interval_mem_endpoints p hp0 hp1 t).symm.trans hright.symm))
  have hagree (x : V2) (hx0 : x ∈ squareRimHalfCarrier false)
      (hx1 : x ∈ squareRimHalfCarrier true) :
      (e ⟨x,hx0⟩ : X) = f ⟨x,hx1⟩ := by
    rcases squareRimHalfCarrier_inter.subset ⟨hx0,hx1⟩ with hx | hx
    · have h0 : (⟨x,hx0⟩ : squareRimHalfCarrier false) = p0 0 :=
        Subtype.ext (by simpa [p0] using hx)
      have h1 : (⟨x,hx1⟩ : squareRimHalfCarrier true) = p1 0 :=
        Subtype.ext (by simpa [p1] using hx)
      simp only [h0,h1,e,f,Homeomorph.trans_apply,p0.symm_apply_apply,
        p1.symm_apply_apply,hp0,hq0]
    · have h0 : (⟨x,hx0⟩ : squareRimHalfCarrier false) = p0 1 :=
        Subtype.ext (by simpa [p0] using hx)
      have h1 : (⟨x,hx1⟩ : squareRimHalfCarrier true) = p1 1 :=
        Subtype.ext (by simpa [p1] using hx)
      simp only [h0,h1,e,f,Homeomorph.trans_apply,p0.symm_apply_apply,
        p1.symm_apply_apply,hp1,hq1]
  obtain ⟨H,hH0,hH1⟩ := Homeomorph.exists_union_of_compact
    (isCompact_range (continuous_squareRimHalf false))
    (isCompact_range (continuous_squareRimHalf true)) e f hoverlap hagree
  let G : Q2 ≃ₜ (U ∪ V : Set X) :=
    (Homeomorph.setCongr squareRimHalfCarrier_union.symm).trans H
  let gamma : C(Q2,X) := ⟨fun x => G x,continuous_subtype_val.comp G.continuous⟩
  refine ⟨gamma,fun x y h => G.injective (Subtype.ext h),?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (G y).property
    · intro hx
      obtain ⟨y,hy⟩ := G.surjective ⟨x,hx⟩
      exact ⟨y,congrArg Subtype.val hy⟩
  · intro t
    have hh := hH0 (p0 t)
    change gamma (squareRimLoop (squareRimHalfTime false t)) = (p (p0.symm (p0 t)) : X) at hh
    simpa only [p0.symm_apply_apply] using hh
  · intro t
    have hh := hH1 (p1 t)
    change gamma (squareRimLoop (squareRimHalfTime true t)) = (q (p1.symm (p1 t)) : X) at hh
    simpa only [p1.symm_apply_apply] using hh

theorem exists_two_original_arc_loop
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hV : IsFinitePLBallPair ℝ V {c,d})
    (hab : a ≠ b) (hcd : c ≠ d) {f g : (ℝ × ℝ) → X}
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hfi : InjOn f U) (hgi : InjOn g V)
    (h0 : f a = g c) (h1 : f b = g d)
    (hinter : f '' U ∩ g '' V = {f a,f b}) :
    ∃ gamma : C(Q2,X), Function.Injective gamma ∧ range gamma = f '' U ∪ g '' V := by
  obtain ⟨p,_,hp0,hp1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨q,_,hq0,hq1⟩ := hV.exists_unitInterval_chart_with_endpoints hcd
  let := p.compactSpace
  let := q.compactSpace
  have hfemb : Topology.IsEmbedding (fun x : U => f x) :=
    (hf.domRestrict.isClosedEmbedding (fun x y h => Subtype.ext (hfi x.property y.property h))).isEmbedding
  have hgemb : Topology.IsEmbedding (fun x : V => g x) :=
    (hg.domRestrict.isClosedEmbedding (fun x y h => Subtype.ext (hgi x.property y.property h))).isEmbedding
  have hrangef : range (fun x : U => f x) = f '' U := by ext x; simp
  have hrangeg : range (fun x : V => g x) = g '' V := by ext x; simp
  let pf := p.trans (hfemb.toHomeomorph.trans (Homeomorph.setCongr hrangef))
  let qg := q.trans (hgemb.toHomeomorph.trans (Homeomorph.setCongr hrangeg))
  have hpf0 : (pf (0 : unitInterval) : X) = f a := congrArg f hp0
  have hpf1 : (pf (1 : unitInterval) : X) = f b := congrArg f hp1
  have hqg0 : (qg (0 : unitInterval) : X) = f a := (congrArg g hq0).trans h0.symm
  have hqg1 : (qg (1 : unitInterval) : X) = f b := (congrArg g hq1).trans h1.symm
  obtain ⟨gamma,hgamma,hrange,_,_⟩ := exists_two_arc_loop hinter pf qg hpf0 hpf1 hqg0 hqg1
  exact ⟨gamma,hgamma,hrange⟩

end PoincareConjecture.M76
