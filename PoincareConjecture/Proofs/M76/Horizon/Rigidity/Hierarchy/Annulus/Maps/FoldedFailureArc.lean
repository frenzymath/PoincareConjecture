import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhasePLArcs

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private theorem covering_endpoints_eq_of_comp_contractible
    {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    (g : C(E, Y)) (hg : IsCoveringMap g) (b : C(unitInterval, E)) (y : Y)
    (F : (g.comp b).HomotopyRel (ContinuousMap.const unitInterval y)
      ({0, 1} : Set unitInterval)) : b 0 = b 1 := by
  have h0 : (g.comp b) 0 = g (b 0) := rfl
  have h1 : y = g (b 0) :=
    (F.fst_eq_snd (show (0 : unitInterval) ∈ ({0, 1} : Set unitInterval) from
      Or.inl rfl)).symm
  have hb : b = hg.liftPath (g.comp b) (b 0) h0 :=
    (hg.eq_liftPath_iff' h0).mpr ⟨rfl, rfl⟩
  have he := hg.liftPath_apply_one_eq_of_homotopicRel ⟨F⟩ (b 0) h0 h1
  rw [← hb, hg.liftPath_const h1] at he
  exact he.symm

theorem hamiltonZero_failure_arc_not_boundary_homotopic
    (psi : C(H0, H0)) {R : Set X0}
    (g : C(frontier R, C0 × C0)) (hg : IsCoveringMap g)
    (hgval : ∀ x : frontier R, g x = (Q0 (hamiltonZeroAmbientMap psi x)).1)
    (k : C(unitInterval, X0)) (hne : k 0 ≠ k 1) (v : X0)
    (F : ((hamiltonZeroAmbientMap psi).comp k).HomotopyRel
      (ContinuousMap.const unitInterval v) ({0, 1} : Set unitInterval)) :
    ¬ ∃ b : C(unitInterval, frontier R),
      Nonempty (((⟨Subtype.val, continuous_subtype_val⟩ : C(frontier R, X0)).comp b).HomotopyRel
        k ({0, 1} : Set unitInterval)) := by
  rintro ⟨b, ⟨G⟩⟩
  let tangent : C(X0, C0 × C0) := ⟨fun x => (Q0 x).1, by fun_prop⟩
  let ambient := hamiltonZeroAmbientMap psi
  let incl : C(frontier R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  have hstart : tangent.comp (ambient.comp (incl.comp b)) = g.comp b := by
    apply ContinuousMap.ext
    intro t
    exact (hgval (b t)).symm
  have hend : tangent.comp (ContinuousMap.const unitInterval v) =
      ContinuousMap.const unitInterval (tangent v) := rfl
  let contraction := ((G.compContinuousMap ambient).trans F).compContinuousMap tangent
  have hb := covering_endpoints_eq_of_comp_contractible g hg b (tangent v)
    (contraction.cast hstart hend)
  have he0 := G.fst_eq_snd (show (0 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inl rfl)
  have he1 := G.fst_eq_snd (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inr rfl)
  exact hne (he0.symm.trans ((congrArg Subtype.val hb).trans he1))

theorem exists_hamiltonZero_source_annulus_normal_form_with_failure_arc
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi psi : C(H0, H0))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {R A : Set X0} (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other})))
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    {S : Set X0} (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = S)
    (H : Ann ≃ₜ S) (j : ℝ × ℝ → X0) (hj : PolyhedralPLInCharts e j Ann)
    (hJ : ∀ z : Ann, j z = (H z : X0))
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X0) ∈ frontier R)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (halphabeta : alpha < beta)
    (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)}) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap psi (j z),
      (hamiltonZeroAmbientMap psi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
      ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
        ∃ q : ℝ × ℝ → X0, PolyhedralPLInCharts d q Ann ∧
          (∀ z : Ann, q z = hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) ∧
          Nonempty (u.HomotopyRel
            ((hamiltonZeroAnnulusTargetMap delta0 delta1 theta).comp c) Dehn.annulusRims) ∧
          (delta0 = delta1 → ∀ xi : C0,
            ∃ (k : C(unitInterval, X0)) (param : ℝ → ℝ × ℝ),
              Topology.IsEmbedding k ∧
              FinitePiecewiseAffineOn param (Icc (0 : ℝ) 1) ∧
              PolyhedralPLInCharts e (j ∘ param) (Icc (0 : ℝ) 1) ∧
              (∀ t : unitInterval, param t ∈ Ann ∧ j (param t) = k t) ∧
              range k ⊆ S ∧
              (∀ t, k t ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
              (∀ t, k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1) ∧
              k 0 ≠ k 1 ∧
              (∀ t : unitInterval, q (param t) = (Q0).symm ((xi, theta), (delta0 : C0))) ∧
              hamiltonZeroAmbientMap psi (k 0) = (Q0).symm ((xi, theta), (delta0 : C0)) ∧
              hamiltonZeroAmbientMap psi (k 1) = (Q0).symm ((xi, theta), (delta0 : C0)) ∧
              Nonempty (((hamiltonZeroAmbientMap psi).comp k).HomotopyRel
                (ContinuousMap.const unitInterval ((Q0).symm ((xi, theta), (delta0 : C0))))
                ({0, 1} : Set unitInterval))) := by
  classical
  intro u
  obtain ⟨delta0, hd0, delta1, hd1, c, hc, q, hq, hqval, hhom, hfibers⟩ :=
    exists_hamiltonZero_source_annulus_normal_form_with_PL_arcs hd phi psi hpsi
      heR hA hAR hfixed hne hreg hN hfront hcover hS hcomponent H j hj hJ hmark
      halpha halphabeta hbeta hR hRfront
  refine ⟨delta0, hd0, delta1, hd1, c, hc, q, hq, hqval, hhom, ?_⟩
  intro hfold xi
  subst delta1
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  have hcsurj : Function.Surjective c := by
    apply range_eq_univ.mp
    apply IsClopen.eq_univ
      ⟨(isCompact_range c.continuous).isClosed, hc.isOpenMap.isOpen_range⟩
    exact ⟨c (Dehn.annulusRimPoint false 0), mem_range_self _⟩
  obtain ⟨z, hz⟩ := hcsurj (0, xi)
  obtain ⟨n, arc, param, hi, hparamPL, hparam, hjparam, _, hwhole, hends⟩ := hfibers xi
  have hzfiber : z ∈ ⋃ i, range (arc i) := by
    rw [hwhole]
    exact congrArg Prod.snd hz
  obtain ⟨i, _, _⟩ := mem_iUnion.mp hzfiber
  have hfiber (t : unitInterval) : (c (arc i t)).2 = xi := by
    change arc i t ∈ {x | (c x).2 = xi}
    rw [← hwhole]
    exact mem_iUnion.mpr ⟨i, mem_range_self t⟩
  let k : C(unitInterval, X0) :=
    ⟨fun t => (H (arc i t) : X0), by fun_prop⟩
  have hkv (t : unitInterval) : j (param i t) = k t := by
    rw [hparam i t, hJ]
    rfl
  have hkemb : Topology.IsEmbedding k :=
    (Topology.IsEmbedding.subtypeVal.comp H.isEmbedding).comp (hi i)
  have hkS : range k ⊆ S := by
    rintro _ ⟨t, rfl⟩
    exact (H (arc i t)).property
  have hkfront (t : unitInterval) : k t ∈ frontier R ↔ t = 0 ∨ t = 1 := by
    rw [← hkv, hparam]
    exact hends i t
  have hkint (t : unitInterval) : k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1 := by
    have hmem := (hS (hkS (mem_range_self t))).1
    have hf : k t ∈ frontier R ↔ k t ∉ interior R := by
      rw [heR.closed.frontier_eq]
      exact and_iff_right hmem
    rw [← not_or, ← hkfront, hf, not_not]
  have hkneq : k 0 ≠ k 1 := fun hh => zero_ne_one (hkemb.injective hh)
  have hv (t : unitInterval) :
      hamiltonZeroAnnulusTargetMap delta0 delta0 theta (c (arc i t)) =
        (Q0).symm ((xi, theta), (delta0 : C0)) := by
    simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk, sub_self,
      zero_mul, zero_add, hfiber]
  have hrim (t : unitInterval) (ht : t = 0 ∨ t = 1) : arc i t ∈ Dehn.annulusRims := by
    rw [Dehn.annulusRims, mem_union, Dehn.range_annulusRimPoint, Dehn.range_annulusRimPoint]
    exact (hmark _).mpr (by rw [← hJ]; exact (hends i t).mpr ht)
  obtain ⟨F⟩ := hhom
  have hend (t : unitInterval) (ht : t = 0 ∨ t = 1) :
      hamiltonZeroAmbientMap psi (k t) = (Q0).symm ((xi, theta), (delta0 : C0)) := by
    have hh := F.fst_eq_snd (hrim t ht)
    change hamiltonZeroAmbientMap psi (j (arc i t)) = _ at hh
    rw [hJ] at hh
    exact hh.trans (hv t)
  let G : ((hamiltonZeroAmbientMap psi).comp k).HomotopyRel
      (ContinuousMap.const unitInterval ((Q0).symm ((xi, theta), (delta0 : C0))))
      ({0, 1} : Set unitInterval) :=
    { toFun := fun x => F (x.1, arc i x.2)
      continuous_toFun := F.continuous.comp (continuous_fst.prodMk ((arc i).continuous.comp continuous_snd))
      map_zero_left := by
        intro t
        rw [F.apply_zero]
        change hamiltonZeroAmbientMap psi (j (arc i t)) = hamiltonZeroAmbientMap psi (k t)
        rw [hJ]
        rfl
      map_one_left := by intro t; rw [F.apply_one]; exact hv t
      prop' := by
        intro s t ht
        have ht' : t = 0 ∨ t = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using ht
        change F (s, arc i t) = hamiltonZeroAmbientMap psi (k t)
        rw [F.eq_fst s (hrim t ht')]
        change hamiltonZeroAmbientMap psi (j (arc i t)) = _
        rw [hJ]
        rfl }
  refine ⟨k, param i, hkemb, hparamPL i, hjparam i, ?_, hkS, hkfront, hkint, hkneq,
    ?_, hend 0 (Or.inl rfl), hend 1 (Or.inr rfl), ⟨G⟩⟩
  · intro t
    exact ⟨by rw [hparam]; exact (arc i t).property, hkv t⟩
  · intro t
    rw [hparam, hqval]
    exact hv t

end PoincareConjecture.M76
