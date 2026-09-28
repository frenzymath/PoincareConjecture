import PoincareConjecture.Proofs.M83.LocalOrientationGluing
import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

private def chartMap {X : Type u} {Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) : C(e.source, Y) :=
  ⟨e.source.domRestrict e, e.continuousOn.domRestrict⟩

private def chartInclusion {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X X) : C(e.source, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def inclusionMap {X : Type u} [TopologicalSpace X]
    {Y : Type u} [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) :
    C(e.source, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem localOrientation_pullback_eq_of_eq
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O : LocalOrientation Y) (f g : C(X, Y))
    (hf : _root_.Topology.IsOpenEmbedding f)
    (hg : _root_.Topology.IsOpenEmbedding g) (hfg : f = g) (x : X) :
    (O.pullback f hf).atPoint x = (O.pullback g hg).atPoint x := by
  subst g
  rfl

def IsLocalOrientationLift
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    (f : X → Y) (O : LocalOrientation Y) (Q : LocalOrientation X) : Prop :=
  ∀ (x : X) (e : OpenPartialHomeomorph X Y) (hx : x ∈ e.source) (_hfe : f = e),
    localHomologyMap (chartMap e) e.isOpenEmbedding_restrict.injective
      ⟨x, hx⟩ 3
      ((localHomologyEquiv (inclusionMap e)
        e.open_source.isOpenEmbedding_subtypeVal ⟨x, hx⟩ 3).symm
        (Q.atPoint x)) = O.atPoint ((chartMap e) ⟨x, hx⟩)

private theorem chart_overlap_compat
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace Y]
    (O : LocalOrientation Y) (e₁ e₂ : OpenPartialHomeomorph X Y)
    [LocallyCompactSpace e₁.source] [LocallyCompactSpace e₂.source]
    [LocallyCompactSpace ↥(e₁.source ∩ e₂.source)]
    (h₁ : ∀ x, e₁ x = e₂ x) (x : X)
    (hx₁ : x ∈ e₁.source) (hx₂ : x ∈ e₂.source) :
    let W := e₁.source ∩ e₂.source
    let z : W := ⟨x, hx₁, hx₂⟩
    ((O.pullback (chartMap e₁) e₁.isOpenEmbedding_restrict).pullback
      (⟨fun w : W => ⟨w.1, w.2.1⟩,
        continuous_subtype_val.subtype_mk _⟩)
      (by
        apply e₁.open_source.isOpenEmbedding_subtypeVal.of_comp
        change _root_.Topology.IsOpenEmbedding
          ((e₁.source ∩ e₂.source).domRestrict (fun w : X => w))
        exact (e₁.open_source.inter e₂.open_source).isOpenEmbedding_subtypeVal)).atPoint z =
      ((O.pullback (chartMap e₂) e₂.isOpenEmbedding_restrict).pullback
      (⟨fun w : W => ⟨w.1, w.2.2⟩,
        continuous_subtype_val.subtype_mk _⟩)
      (by
        apply e₂.open_source.isOpenEmbedding_subtypeVal.of_comp
        change _root_.Topology.IsOpenEmbedding
          ((e₁.source ∩ e₂.source).domRestrict (fun w : X => w))
        exact (e₁.open_source.inter e₂.open_source).isOpenEmbedding_subtypeVal)).atPoint z := by
  let W := e₁.source ∩ e₂.source
  let z : W := ⟨x, hx₁, hx₂⟩
  let w₁ : C(W, e₁.source) :=
    ⟨fun w => ⟨w.1, w.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  let w₂ : C(W, e₂.source) :=
    ⟨fun w => ⟨w.1, w.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hw₁ : _root_.Topology.IsOpenEmbedding w₁ := by
    apply e₁.open_source.isOpenEmbedding_subtypeVal.of_comp w₁
    change _root_.Topology.IsOpenEmbedding
      ((e₁.source ∩ e₂.source).domRestrict (fun w : X => w))
    exact (e₁.open_source.inter e₂.open_source).isOpenEmbedding_subtypeVal
  have hw₂ : _root_.Topology.IsOpenEmbedding w₂ := by
    apply e₂.open_source.isOpenEmbedding_subtypeVal.of_comp w₂
    change _root_.Topology.IsOpenEmbedding
      ((e₁.source ∩ e₂.source).domRestrict (fun w : X => w))
    exact (e₁.open_source.inter e₂.open_source).isOpenEmbedding_subtypeVal
  let c₁ := (chartMap e₁).comp w₁
  let c₂ := (chartMap e₂).comp w₂
  have hc₁ : _root_.Topology.IsOpenEmbedding c₁ := by
    exact e₁.isOpenEmbedding_restrict.comp hw₁
  have hc₂ : _root_.Topology.IsOpenEmbedding c₂ := by
    exact e₂.isOpenEmbedding_restrict.comp hw₂
  have hcomp : c₁ = c₂ := by
    ext w
    exact h₁ w.1
  have hleft := LocalOrientation.pullback_comp O w₁ (chartMap e₁)
    hw₁ e₁.isOpenEmbedding_restrict z
  have hlocal :
      ((O.pullback (chartMap e₁) e₁.isOpenEmbedding_restrict).pullback w₁ hw₁).atPoint z =
        ((O.pullback (chartMap e₂) e₂.isOpenEmbedding_restrict).pullback w₂ hw₂).atPoint z := by
    have hsame : (O.pullback c₁ hc₁).atPoint z =
        (O.pullback c₂ hc₂).atPoint z := by
      exact localOrientation_pullback_eq_of_eq O c₁ c₂ hc₁ hc₂ hcomp z
    have hright := LocalOrientation.pullback_comp O w₂ (chartMap e₂)
      hw₂ e₂.isOpenEmbedding_restrict z
    exact hleft.trans (hsame.trans hright.symm)
  exact hlocal

theorem exists_localOrientation_of_isLocalHomeomorph
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (f : X → Y) (hf : IsLocalHomeomorph f) (O : LocalOrientation Y) :
    ∃ Q : LocalOrientation X,
      ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, ∃ hx : x ∈ e.source, f = e ∧
        localHomologyMap (chartMap e) e.isOpenEmbedding_restrict.injective
          ⟨x, hx⟩ 3
          ((localHomologyEquiv
            (⟨Subtype.val, continuous_subtype_val⟩ : C(e.source, X))
            e.open_source.isOpenEmbedding_subtypeVal
            ⟨x, hx⟩ 3).symm
            (Q.atPoint x)) = O.atPoint ((chartMap e) ⟨x, hx⟩) := by
  let e (x : X) : OpenPartialHomeomorph X Y := (hf x).choose
  have he (x : X) : x ∈ (e x).source := (hf x).choose_spec.1
  have hfe (x : X) : f = e x := (hf x).choose_spec.2
  let U (x : X) : Set X := (e x).source
  let Oloc : ∀ x : X, LocalOrientation (U x) := fun x => by
    letI : LocallyCompactSpace (U x) := (e x).open_source.locallyCompactSpace
    exact O.pullback (chartMap (e x)) (e x).isOpenEmbedding_restrict
  have hU : ∀ x : X, IsOpen (U x) := fun x => (e x).open_source
  have hcover : ∀ x : X, ∃ i : X, x ∈ U i := fun x => ⟨x, he x⟩
  have hcompat : ∀ (i j : X) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (Oloc i).inclusionClass ⟨x, hi⟩ = (Oloc j).inclusionClass ⟨x, hj⟩ := by
    intro i j x hi hj
    let W := U i ∩ U j
    let z : W := ⟨x, hi, hj⟩
    let : LocallyCompactSpace (U i) := (e i).open_source.locallyCompactSpace
    let : LocallyCompactSpace (U j) := (e j).open_source.locallyCompactSpace
    let : LocallyCompactSpace W := (hU i |>.inter (hU j)).locallyCompactSpace
    let wᵢ : C(W, U i) :=
      ⟨fun w => ⟨w.1, w.2.1⟩, continuous_subtype_val.subtype_mk _⟩
    let wⱼ : C(W, U j) :=
      ⟨fun w => ⟨w.1, w.2.2⟩, continuous_subtype_val.subtype_mk _⟩
    have hwᵢ : _root_.Topology.IsOpenEmbedding wᵢ := by
      apply (hU i).isOpenEmbedding_subtypeVal.of_comp wᵢ
      change _root_.Topology.IsOpenEmbedding
        ((U i ∩ U j).domRestrict (fun w : X => w))
      exact (hU i |>.inter (hU j)).isOpenEmbedding_subtypeVal
    have hwⱼ : _root_.Topology.IsOpenEmbedding wⱼ := by
      apply (hU j).isOpenEmbedding_subtypeVal.of_comp wⱼ
      change _root_.Topology.IsOpenEmbedding
        ((U i ∩ U j).domRestrict (fun w : X => w))
      exact (hU i |>.inter (hU j)).isOpenEmbedding_subtypeVal
    let incW : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hincW : _root_.Topology.IsOpenEmbedding incW :=
      (hU i |>.inter (hU j)).isOpenEmbedding_subtypeVal
    let incᵢ : C(U i, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let incⱼ : C(U j, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hincᵢ : Function.Injective incᵢ := Subtype.val_injective
    have hincⱼ : Function.Injective incⱼ := Subtype.val_injective
    have hci : incᵢ.comp wᵢ = incW := by ext w; rfl
    have hcj : incⱼ.comp wⱼ = incW := by ext w; rfl
    have hli := congrArg (fun k => k (((Oloc i).pullback wᵢ hwᵢ).atPoint z))
      (localHomologyMap_comp wᵢ incᵢ hwᵢ.injective hincᵢ z 3)
    have hlj := congrArg (fun k => k (((Oloc j).pullback wⱼ hwⱼ).atPoint z))
      (localHomologyMap_comp wⱼ incⱼ hwⱼ.injective hincⱼ z 3)
    rw [ModuleCat.comp_apply, LocalOrientation.map_pullback] at hli
    rw [ModuleCat.comp_apply, LocalOrientation.map_pullback] at hlj
    have hli' : (Oloc i).inclusionClass ⟨x, hi⟩ =
        localHomologyMap incW hincW.injective z 3 (((Oloc i).pullback wᵢ hwᵢ).atPoint z) := by
      have hmap_eq : localHomologyMap (incᵢ.comp wᵢ)
          (hincᵢ.comp hwᵢ.injective) z 3 (((Oloc i).pullback wᵢ hwᵢ).atPoint z) =
          localHomologyMap incW hincW.injective z 3
            (((Oloc i).pullback wᵢ hwᵢ).atPoint z) := by
        cases hci
        rfl
      simpa [LocalOrientation.inclusionClass, incW, incᵢ, wᵢ, z] using hli.trans hmap_eq
    have hlj' : (Oloc j).inclusionClass ⟨x, hj⟩ =
        localHomologyMap incW hincW.injective z 3 (((Oloc j).pullback wⱼ hwⱼ).atPoint z) := by
      have hmap_eq : localHomologyMap (incⱼ.comp wⱼ)
          (hincⱼ.comp hwⱼ.injective) z 3 (((Oloc j).pullback wⱼ hwⱼ).atPoint z) =
          localHomologyMap incW hincW.injective z 3
            (((Oloc j).pullback wⱼ hwⱼ).atPoint z) := by
        cases hcj
        rfl
      simpa [LocalOrientation.inclusionClass, incW, incⱼ, wⱼ, z] using hlj.trans hmap_eq
    have hlocal := chart_overlap_compat O (e i) (e j)
      (fun y => by rw [← hfe i, ← hfe j]) x hi hj
    have hlocal' :
        ((Oloc i).pullback wᵢ hwᵢ).atPoint z =
          ((Oloc j).pullback wⱼ hwⱼ).atPoint z := by
      simpa [Oloc, U, wᵢ, wⱼ] using hlocal
    have hmaps := congrArg (fun q => localHomologyMap incW hincW.injective z 3 q)
      hlocal'
    exact hli'.trans (hmaps.trans hlj'.symm)
  let Q := LocalOrientation.glue U hU Oloc hcover hcompat
  refine ⟨Q, ?_⟩
  intro x
  let ex := e x
  let hx := he x
  let : LocallyCompactSpace ex.source := ex.open_source.locallyCompactSpace
  let inc : C(ex.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let einc : _root_.Topology.IsOpenEmbedding inc := ex.open_source.isOpenEmbedding_subtypeVal
  let z : ex.source := ⟨x, hx⟩
  refine ⟨ex, hx, hfe x, ?_⟩
  have hglue := LocalOrientation.glue_atPoint U hU Oloc hcover hcompat x x hx
  have hmap := LocalOrientation.map_pullback O (chartMap ex)
    ex.isOpenEmbedding_restrict z
  change localHomologyMap (chartMap ex) ex.isOpenEmbedding_restrict.injective z 3
    ((localHomologyEquiv inc einc z 3).symm (Q.atPoint x)) = O.atPoint ((chartMap ex) z)
  have hinv : (localHomologyEquiv inc einc z 3).symm (Q.atPoint x) =
      (Oloc x).atPoint z := by
    apply (localHomologyEquiv inc einc z 3).injective
    rw [LinearEquiv.apply_symm_apply, hglue]
    rfl
  rw [hinv]
  exact hmap

theorem exists_localOrientation_lift_of_isLocalHomeomorph
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (f : X → Y) (hf : IsLocalHomeomorph f) (O : LocalOrientation Y) :
    ∃ Q : LocalOrientation X, IsLocalOrientationLift f O Q := by
  let I := {e : OpenPartialHomeomorph X Y // f = e}
  let U : I → Set X := fun i => i.1.source
  let Oloc : ∀ i : I, LocalOrientation (U i) := fun i => by
    letI : LocallyCompactSpace (U i) := i.1.open_source.locallyCompactSpace
    exact O.pullback (chartMap i.1) i.1.isOpenEmbedding_restrict
  have hU : ∀ i : I, IsOpen (U i) := fun i => i.1.open_source
  have hcover : ∀ x : X, ∃ i : I, x ∈ U i := by
    intro x
    obtain ⟨e, hx, hfe⟩ := hf x
    exact ⟨⟨e, hfe⟩, hx⟩
  have hcompat : ∀ (i j : I) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      (Oloc i).inclusionClass ⟨x, hi⟩ = (Oloc j).inclusionClass ⟨x, hj⟩ := by
    intro i j x hi hj
    let W := U i ∩ U j
    let z : W := ⟨x, hi, hj⟩
    let : LocallyCompactSpace (U i) := i.1.open_source.locallyCompactSpace
    let : LocallyCompactSpace (U j) := j.1.open_source.locallyCompactSpace
    let : LocallyCompactSpace W := (hU i |>.inter (hU j)).locallyCompactSpace
    let wᵢ : C(W, U i) :=
      ⟨fun w => ⟨w.1, w.2.1⟩, continuous_subtype_val.subtype_mk _⟩
    let wⱼ : C(W, U j) :=
      ⟨fun w => ⟨w.1, w.2.2⟩, continuous_subtype_val.subtype_mk _⟩
    have hwᵢ : _root_.Topology.IsOpenEmbedding wᵢ := by
      apply (hU i).isOpenEmbedding_subtypeVal.of_comp wᵢ
      change _root_.Topology.IsOpenEmbedding
        ((U i ∩ U j).domRestrict (fun w : X => w))
      exact (hU i |>.inter (hU j)).isOpenEmbedding_subtypeVal
    have hwⱼ : _root_.Topology.IsOpenEmbedding wⱼ := by
      apply (hU j).isOpenEmbedding_subtypeVal.of_comp wⱼ
      change _root_.Topology.IsOpenEmbedding
        ((U i ∩ U j).domRestrict (fun w : X => w))
      exact (hU i |>.inter (hU j)).isOpenEmbedding_subtypeVal
    let incW : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hincW : _root_.Topology.IsOpenEmbedding incW :=
      (hU i |>.inter (hU j)).isOpenEmbedding_subtypeVal
    let incᵢ : C(U i, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let incⱼ : C(U j, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hincᵢ : Function.Injective incᵢ := Subtype.val_injective
    have hincⱼ : Function.Injective incⱼ := Subtype.val_injective
    have hci : incᵢ.comp wᵢ = incW := by ext w; rfl
    have hcj : incⱼ.comp wⱼ = incW := by ext w; rfl
    have hli := congrArg (fun k => k (((Oloc i).pullback wᵢ hwᵢ).atPoint z))
      (localHomologyMap_comp wᵢ incᵢ hwᵢ.injective hincᵢ z 3)
    have hlj := congrArg (fun k => k (((Oloc j).pullback wⱼ hwⱼ).atPoint z))
      (localHomologyMap_comp wⱼ incⱼ hwⱼ.injective hincⱼ z 3)
    rw [ModuleCat.comp_apply, LocalOrientation.map_pullback] at hli
    rw [ModuleCat.comp_apply, LocalOrientation.map_pullback] at hlj
    have hli' : (Oloc i).inclusionClass ⟨x, hi⟩ =
        localHomologyMap incW hincW.injective z 3 (((Oloc i).pullback wᵢ hwᵢ).atPoint z) := by
      have hmap_eq : localHomologyMap (incᵢ.comp wᵢ)
          (hincᵢ.comp hwᵢ.injective) z 3 (((Oloc i).pullback wᵢ hwᵢ).atPoint z) =
          localHomologyMap incW hincW.injective z 3
            (((Oloc i).pullback wᵢ hwᵢ).atPoint z) := by
        cases hci
        rfl
      simpa [LocalOrientation.inclusionClass, incW, incᵢ, wᵢ, z] using hli.trans hmap_eq
    have hlj' : (Oloc j).inclusionClass ⟨x, hj⟩ =
        localHomologyMap incW hincW.injective z 3 (((Oloc j).pullback wⱼ hwⱼ).atPoint z) := by
      have hmap_eq : localHomologyMap (incⱼ.comp wⱼ)
          (hincⱼ.comp hwⱼ.injective) z 3 (((Oloc j).pullback wⱼ hwⱼ).atPoint z) =
          localHomologyMap incW hincW.injective z 3
            (((Oloc j).pullback wⱼ hwⱼ).atPoint z) := by
        cases hcj
        rfl
      simpa [LocalOrientation.inclusionClass, incW, incⱼ, wⱼ, z] using hlj.trans hmap_eq
    have hlocal := chart_overlap_compat O i.1 j.1
      (fun y => by rw [← i.2, ← j.2]) x hi hj
    have hlocal' :
        ((Oloc i).pullback wᵢ hwᵢ).atPoint z =
          ((Oloc j).pullback wⱼ hwⱼ).atPoint z := by
      simpa [Oloc, U, wᵢ, wⱼ] using hlocal
    have hmaps := congrArg (fun q => localHomologyMap incW hincW.injective z 3 q)
      hlocal'
    exact hli'.trans (hmaps.trans hlj'.symm)
  let Q := LocalOrientation.glue U hU Oloc hcover hcompat
  refine ⟨Q, ?_⟩
  unfold IsLocalOrientationLift
  intro x e hx hfe
  let i : I := ⟨e, hfe⟩
  let : LocallyCompactSpace e.source := e.open_source.locallyCompactSpace
  let inc : C(e.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let hinc : _root_.Topology.IsOpenEmbedding inc := e.open_source.isOpenEmbedding_subtypeVal
  let z : e.source := ⟨x, hx⟩
  have hglue := LocalOrientation.glue_atPoint U hU Oloc hcover hcompat i x hx
  have hmap := LocalOrientation.map_pullback O (chartMap e)
    e.isOpenEmbedding_restrict z
  change localHomologyMap (chartMap e) e.isOpenEmbedding_restrict.injective z 3
    ((localHomologyEquiv inc hinc z 3).symm (Q.atPoint x)) = O.atPoint ((chartMap e) z)
  have hinv : (localHomologyEquiv inc hinc z 3).symm (Q.atPoint x) =
      (Oloc i).atPoint z := by
    apply (localHomologyEquiv inc hinc z 3).injective
    rw [LinearEquiv.apply_symm_apply, hglue]
    rfl
  rw [hinv]
  exact hmap

theorem localHomologyMap_eq_of_lift
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (p : X → Y) (hp : IsLocalHomeomorph p) (O : LocalOrientation Y)
    (Q : LocalOrientation X) (hQ : IsLocalOrientationLift p O Q)
    (τ : X ≃ₜ X) (hfix : ∀ x, p (τ x) = p x) (x : X) :
    localHomologyMap (⟨τ, τ.continuous⟩ : C(X, X)) τ.injective x 3
      (Q.atPoint x) = Q.atPoint (τ x) := by
  obtain ⟨e, he, hpe⟩ := hp (τ x)
  let et := τ.toOpenPartialHomeomorph.trans e
  have het : x ∈ et.source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨by simp, he⟩
  have hpet : p = et := by
    funext y
    calc
      p y = p (τ y) := (hfix y).symm
      _ = e (τ y) := congrFun hpe (τ y)
      _ = et y := rfl
  have hlift_t := hQ x et het hpet
  have hlift_e := hQ (τ x) e he hpe
  let aT : C(et.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let aE : C(e.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let u : C(et.source, e.source) :=
    ⟨fun z => ⟨τ z.1, by
      exact z.2.2⟩, by fun_prop⟩
  let hA : _root_.Topology.IsOpenEmbedding aT := et.open_source.isOpenEmbedding_subtypeVal
  let hB : _root_.Topology.IsOpenEmbedding aE := e.open_source.isOpenEmbedding_subtypeVal
  let tmap : C(X, X) := ⟨τ, τ.continuous⟩
  have htu : tmap.comp aT = aE.comp u := by
    ext z
    rfl
  have hu : _root_.Topology.IsOpenEmbedding u := by
    apply _root_.Topology.IsOpenEmbedding.of_comp u hB
    change _root_.Topology.IsOpenEmbedding (tmap.comp aT)
    exact τ.isOpenEmbedding.comp hA
  let zT : et.source := ⟨x, het⟩
  let zE : e.source := ⟨τ x, he⟩
  let qT := (localHomologyEquiv aT hA zT 3).symm (Q.atPoint x)
  let qE := (localHomologyEquiv aE hB zE 3).symm (Q.atPoint (τ x))
  have hT : localHomologyMap (chartMap et) et.isOpenEmbedding_restrict.injective
      zT 3 qT = O.atPoint ((chartMap et) zT) := by
    simpa [qT, zT, aT, inclusionMap] using hlift_t
  have hE : localHomologyMap (chartMap e) e.isOpenEmbedding_restrict.injective
      zE 3 qE = O.atPoint ((chartMap e) zE) := by
    simpa [qE, zE, aE, inclusionMap] using hlift_e
  let ce := chartMap e
  let cet := chartMap et
  have hchart : cet = ce.comp u := by
    ext z
    rfl
  have hmap_chart : localHomologyMap cet
      et.isOpenEmbedding_restrict.injective zT 3 =
      localHomologyMap u hu.injective zT 3 ≫
        localHomologyMap ce e.isOpenEmbedding_restrict.injective (u zT) 3 := by
    rw [localHomologyMap_comp]
    cases hchart
    rfl
  have hsame : localHomologyMap ce e.isOpenEmbedding_restrict.injective zE 3
      (localHomologyMap u hu.injective zT 3 qT) =
      localHomologyMap ce e.isOpenEmbedding_restrict.injective zE 3 qE := by
    have ht := congrArg (fun k => k qT) hmap_chart
    rw [ModuleCat.comp_apply] at ht
    exact ht.symm.trans (hT.trans hE.symm)
  have hq : localHomologyMap u hu.injective zT 3 qT = qE := by
    apply (localHomologyEquiv ce e.isOpenEmbedding_restrict zE 3).injective
    exact hsame
  have hincT : localHomologyMap aT hA.injective zT 3 qT = Q.atPoint x := by
    exact (localHomologyEquiv aT hA zT 3).apply_symm_apply _
  have hincE : localHomologyMap aE hB.injective zE 3 qE = Q.atPoint (τ x) := by
    exact (localHomologyEquiv aE hB zE 3).apply_symm_apply _
  have hcomp' : localHomologyMap aT hA.injective zT 3 ≫
      localHomologyMap tmap τ.injective x 3 =
      localHomologyMap u hu.injective zT 3 ≫
        localHomologyMap aE hB.injective zE 3 := by
    exact (localHomologyMap_comp aT tmap hA.injective τ.injective zT 3).trans
      (localHomologyMap_comp u aE hu.injective hB.injective zT 3).symm
  have hfinal := congrArg (fun k => k qT) hcomp'
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hincT, hq] at hfinal
  exact hfinal.trans hincE

end PoincareConjecture.Proofs.M83
