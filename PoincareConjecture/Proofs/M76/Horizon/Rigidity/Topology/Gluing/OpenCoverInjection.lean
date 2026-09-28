import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Gluing.OverlapTransport
import PoincareConjecture.Proofs.M54.Mathlib.VanKampenRetraction











set_option autoImplicit false

open Set
open scoped unitInterval

namespace PoincareConjecture.M76.IncompressibleGluing

variable {X : Type*} [TopologicalSpace X]

private noncomputable def componentRepresentationTransport {A : Type*} [Group A]
    (a : (∀ c, ComponentGroup X c) →* A) :
    LocalPathTransport (fun _ : Unit => (univ : Set X)) A where
  value p := a (componentTransport p)
  map_const x := by rw [componentTransport_const, map_one]
  square S _ _ := by
    simpa only [map_mul] using congrArg a (componentTransport_square S)

private noncomputable def glueLocalTransports {A : Type*} [Group A]
    (U V : Set X)
    (L : LocalPathTransport (fun _ : Unit => (univ : Set U)) A)
    (R : LocalPathTransport (fun _ : Unit => (univ : Set V)) A)
    (hLR : ∀ (p : C(unitInterval, X)) (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V),
      L.value (p.restrictRange U hU) = R.value (p.restrictRange V hV)) :
    LocalPathTransport (VanKampen.cover U V) A := by
  classical
  let val (p : C(unitInterval, X)) : A :=
    if hp : ∀ t, p t ∈ U then L.value (p.restrictRange U hp)
    else if hp : ∀ t, p t ∈ V then R.value (p.restrictRange V hp) else 1
  have hleft (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ U) :
      val p = L.value (p.restrictRange U hp) := by
    simp only [val, dif_pos hp]
  have hright (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ V) :
      val p = R.value (p.restrictRange V hp) := by
    by_cases h : ∀ t, p t ∈ U
    · rw [hleft p h]; exact hLR p h hp
    · simp only [val, dif_neg h, dif_pos hp]
  refine ⟨val, ?_, ?_⟩
  · intro x
    by_cases hxU : x ∈ U
    · rw [hleft _ (fun _ => hxU)]
      exact L.map_const ⟨x, hxU⟩
    · by_cases hxV : x ∈ V
      · rw [hright _ (fun _ => hxV)]
        exact R.map_const ⟨x, hxV⟩
      · have hnU : ¬ ∀ t : unitInterval, (ContinuousMap.const unitInterval x) t ∈ U :=
          fun h => hxU (h 0)
        have hnV : ¬ ∀ t : unitInterval, (ContinuousMap.const unitInterval x) t ∈ V :=
          fun h => hxV (h 0)
        simp only [val, dif_neg hnU, dif_neg hnV]
  · intro S i hS
    cases i with
    | false =>
      have hU : ∀ z, S z ∈ U := hS
      rw [hleft _ (fun t => hU (t, 0)), hleft _ (fun t => hU (1, t)),
        hleft _ (fun t => hU (0, t)), hleft _ (fun t => hU (t, 1))]
      exact L.square (S.restrictRange U hU) () (fun _ => mem_univ _)
    | true =>
      have hV : ∀ z, S z ∈ V := hS
      rw [hright _ (fun t => hV (t, 0)), hright _ (fun t => hV (1, t)),
        hright _ (fun t => hV (0, t)), hright _ (fun t => hV (t, 1))]
      exact R.square (S.restrictRange V hV) () (fun _ => mem_univ _)

private theorem glueLocalTransports_first {A : Type*} [Group A]
    (U V : Set X)
    (L : LocalPathTransport (fun _ : Unit => (univ : Set U)) A)
    (R : LocalPathTransport (fun _ : Unit => (univ : Set V)) A)
    (hLR : ∀ (p : C(unitInterval, X)) (hU : ∀ t, p t ∈ U) (hV : ∀ t, p t ∈ V),
      L.value (p.restrictRange U hU) = R.value (p.restrictRange V hV))
    (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ U) :
    (glueLocalTransports U V L R hLR).value p = L.value (p.restrictRange U hp) := by
  simp only [glueLocalTransports, dif_pos hp]

set_option backward.isDefEq.respectTransparency false in



theorem inclusion_injective_of_overlap_injective
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hf : ∀ x : (U ∩ V : Set X), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x))
    (hg : ∀ x : (U ∩ V : Set X), Function.Injective
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) x))
    (x : U) : Function.Injective (FundamentalGroup.map (VanKampen.inclusion U) x) := by
  classical
  let GU := ∀ c, ComponentGroup U c
  let GV := ∀ c, ComponentGroup V c
  let A := Equiv.Perm (GU × GV)
  let f : C((U ∩ V : Set X), U) := ContinuousMap.inclusion inter_subset_left
  let g : C((U ∩ V : Set X), V) := ContinuousMap.inclusion inter_subset_right
  let a : GU →* A := regularProduct GU GV
  let b : GV →* A := regularSecond GU GV
  obtain ⟨frame, hframe⟩ := exists_overlap_transport_frame f g hf hg
  let frameV (y : V) : A := if hy : y.1 ∈ U then frame ⟨y.1, hy, y.2⟩ else 1
  let L := componentRepresentationTransport a
  let R := gaugeTransport (componentRepresentationTransport b) frameV
  have hLR (p : C(unitInterval, X)) (hpU : ∀ t, p t ∈ U) (hpV : ∀ t, p t ∈ V) :
      L.value (p.restrictRange U hpU) = R.value (p.restrictRange V hpV) := by
    let pW := p.restrictRange (U ∩ V) (fun t => ⟨hpU t, hpV t⟩)
    have heq := hframe pW
    have hfp : f.comp pW = p.restrictRange U hpU := by ext t; rfl
    have hgp : g.comp pW = p.restrictRange V hpV := by ext t; rfl
    rw [hfp, hgp] at heq
    change a (componentTransport (p.restrictRange U hpU)) =
      frameV ⟨p 0, hpV 0⟩ * b (componentTransport (p.restrictRange V hpV)) *
        (frameV ⟨p 1, hpV 1⟩)⁻¹
    simp only [frameV, dif_pos (hpU 0), dif_pos (hpU 1)]
    convert heq using 1
    congr 1
  let T := glueLocalTransports U V L R hLR
  let Tglobal := T.global (VanKampen.cover_open U V hU hV)
    (VanKampen.cover_covers U V hcover)
  have hrestriction {y z : U} (p : Path y z) :
      Tglobal.value (p.map (VanKampen.inclusion U).continuous).toContinuousMap =
        a (componentTransport p.toContinuousMap) := by
    change T.extend (VanKampen.cover_open U V hU hV)
      (VanKampen.cover_covers U V hcover) _ = _
    rw [T.extend_eq_local (VanKampen.cover_open U V hU hV)
      (VanKampen.cover_covers U V hcover) _ false (fun t => (p t).2)]
    exact glueLocalTransports_first U V L R hLR _ (fun t => (p t).2)
  intro p q hpq
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      have hhom : (p.map (VanKampen.inclusion U).continuous).Homotopic
          (q.map (VanKampen.inclusion U).continuous) := Path.Homotopic.Quotient.eq.mp hpq
      have ht := Tglobal.value_homotopic hhom
      rw [hrestriction, hrestriction] at ht
      have hc := regularProduct_injective (G := GU) GV ht
      have hq : componentLoopTransport x (MulOpposite.op (Path.Homotopic.Quotient.mk p)) =
          componentLoopTransport x (MulOpposite.op (Path.Homotopic.Quotient.mk q)) := by
        simpa only [componentLoopTransport_mk] using hc
      exact MulOpposite.op_injective (componentLoopTransport_injective x hq)

end PoincareConjecture.M76.IncompressibleGluing
